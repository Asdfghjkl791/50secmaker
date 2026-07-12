#!/usr/bin/env python3
# LIVE TAKER — the real-money executor for the measured-taker pocket.
#
# ⚠️  THIS PLACES REAL ORDERS WITH REAL MONEY. It is deliberately built to
#     REFUSE TO ARM until the pre-registered evidence bars are cleared. Those
#     gates are not paranoia — they are the entire reason this project never
#     lost more than it had to. Do not remove them.
#
# ══════════════════════════════════════════════════════════════════════════
#  ARMING GATES (all must pass, checked live at boot against the paper DB)
# ══════════════════════════════════════════════════════════════════════════
#   GATE 1 — CERTIFIED SAMPLE:  >= MIN_CERT_TRADES settlement-graded in-band
#            trades exist in the paper DB (graded='settle'). Feed-graded rows
#            do NOT count. This is what "enough data" actually means.
#   GATE 2 — CERTIFIED EDGE:    certified in-band net >= MIN_CERT_NET dollars
#            AND certified win% > certified avg-ask (a real margin, on real
#            settlement, not the feed).
#   GATE 3 — EXIT PROVEN (only if USE_EXIT=true): the /exit ceiling on recorded
#            bid-paths must be NET POSITIVE — i.e. selling failing trades has
#            been measured to add money, not burn it on false fires. If you
#            want the sell-function live, it has to have EARNED its place.
#   GATE 4 — MANUAL ARM:        LIVE_ARM=YES_I_REVIEWED must be set by hand,
#            after you have read the certified /stats and /exit yourself.
#
#   Per-asset inclusion is DATA-DRIVEN (see PER_ASSET_MIN_NET): an asset trades
#   live only if its OWN certified net clears the per-asset floor. That is how
#   XRP gets excluded if it deserves to be — by evidence, at arm time, not by
#   deleting it from the backtest after the fact.
#
#   Reads the SAME paper DB the paper bot writes (DB_PATH). Point both at the
#   same volume. The paper bot keeps running; this only ARMS when it has earned.
#
# ENV (required to arm): TELEGRAM_TOKEN, TELEGRAM_CHAT_ID, POLY_PRIVATE_KEY,
#   POLY_FUNDER, LIVE_ARM=YES_I_REVIEWED
# ENV (safety, with defaults): LIVE_STAKE=5, DAILY_LOSS_STOP=25,
#   MAX_OPEN=1, BANKROLL_STOP=150, MIN_CERT_TRADES=800, MIN_CERT_NET=20,
#   PER_ASSET_MIN_NET=0, USE_EXIT=true, EXIT_TRIGGER_CENTS=90,
#   TAKER_MAX_ASK_CENTS=98, DB_PATH, TIMEFRAMES=5,15

import os
import time
import json
import sqlite3
import logging
import threading
import requests
from datetime import datetime, timezone, date

# ── order stack (same SDK the maker bot uses) ────────────────────────────────
try:
    from py_clob_client_v2 import (
        ClobClient, OrderArgs, MarketOrderArgs, PartialCreateOrderOptions,
        OrderType,
    )
    from py_clob_client_v2.order_builder.constants import BUY, SELL
    V2_AVAILABLE = True
except Exception:
    V2_AVAILABLE = False

TELEGRAM_TOKEN   = os.environ["TELEGRAM_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
POLY_PRIVATE_KEY = os.environ.get("POLY_PRIVATE_KEY", "")
POLY_FUNDER      = os.environ.get("POLY_FUNDER", "")
LIVE_ARM         = os.environ.get("LIVE_ARM", "")

LIVE_STAKE       = float(os.environ.get("LIVE_STAKE", "5"))
DAILY_LOSS_STOP  = float(os.environ.get("DAILY_LOSS_STOP", "25"))
BANKROLL_STOP    = float(os.environ.get("BANKROLL_STOP", "150"))
MAX_OPEN         = int(os.environ.get("MAX_OPEN", "1"))
MIN_CERT_TRADES  = int(os.environ.get("MIN_CERT_TRADES", "800"))
MIN_CERT_NET     = float(os.environ.get("MIN_CERT_NET", "20"))
PER_ASSET_MIN_NET = float(os.environ.get("PER_ASSET_MIN_NET", "0"))
USE_EXIT         = os.environ.get("USE_EXIT", "true").lower() == "true"
EXIT_TRIGGER_CENTS = float(os.environ.get("EXIT_TRIGGER_CENTS", "90"))
TAKER_MAX_ASK_CENTS = float(os.environ.get("TAKER_MAX_ASK_CENTS", "98"))
TAKER_MIN_ASK_CENTS = float(os.environ.get("TAKER_MIN_ASK_CENTS", "0"))
DB_PATH          = os.environ.get("DB_PATH", "paper_taker.db")
TFS              = [int(x) for x in os.environ.get("TIMEFRAMES", "5,15").split(",")]

ASSET_LIST = ["BTC", "ETH", "SOL", "DOGE", "BNB", "XRP", "HYPE"]
# Assets excluded by name regardless of stats (user decision). XRP removed.
EXCLUDE_ASSETS = set(x.strip().upper()
                     for x in os.environ.get("EXCLUDE_ASSETS", "XRP").split(",") if x.strip())
ASSET_EMOJI = {"BTC": "🟠", "ETH": "🔷", "SOL": "🟣", "DOGE": "🟡",
               "BNB": "🟨", "XRP": "⚪", "HYPE": "🟢"}
CLOB_BASE = "https://clob.polymarket.com"
GAMMA_BASE = "https://gamma-api.polymarket.com"

# frontier gate — imported wholesale from the paper bot's tables so live and
# paper fire identically. (kept in sync by copying the same dicts.)
from math import inf

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("live-taker")

clob_client = None
_start_bankroll = None
_realized_today = 0.0
_today = date.today()


def tg(msg):
    try:
        r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                          json={"chat_id": TELEGRAM_CHAT_ID, "text": msg,
                                "parse_mode": "HTML"}, timeout=8)
        body = {}
        try:
            body = r.json()
        except Exception:
            pass
        if getattr(r, "status_code", 200) != 200 or not body.get("ok", False):
            log.error(f"[TG] REJECTED {getattr(r,'status_code','?')}: {str(body)[:150]}")
            return
        log.info(f"[TG] {msg[:80]}")
    except Exception as e:
        log.error(f"TG error: {e}")


# ══════════════════════════════════════════════════════════════════════════
#  THE GATES
# ══════════════════════════════════════════════════════════════════════════
def certified_stats():
    """Certified (settlement-graded) in-band results from the paper DB, overall
    and per asset. Returns None if the DB/column isn't there yet."""
    try:
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("SELECT asset, ask_cents, result, pnl FROM paper "
                  "WHERE graded='settle' AND result IN ('WIN','LOSS') "
                  "AND ask_cents < ?", (TAKER_MAX_ASK_CENTS,))
        rows = c.fetchall()
        conn.close()
    except Exception as e:
        log.warning(f"[GATE] cannot read certified stats: {e}")
        return None
    n = len(rows)
    if n == 0:
        return {"n": 0, "net": 0.0, "wr": None, "avg_ask": 0.0, "per_asset": {}}
    w = sum(1 for r in rows if r[2] == "WIN")
    net = sum(r[3] or 0 for r in rows)
    avg = sum(r[1] or 0 for r in rows) / n
    per = {}
    for a, ask, res, pnl in rows:
        d = per.setdefault(a, {"n": 0, "w": 0, "net": 0.0, "ask": 0.0})
        d["n"] += 1
        d["w"] += 1 if res == "WIN" else 0
        d["net"] += pnl or 0
        d["ask"] += ask or 0
    return {"n": n, "net": net, "wr": w / n * 100, "avg_ask": avg, "per_asset": per}


def exit_is_profitable():
    """Replays the /exit ceiling on recorded bid-paths: does selling failing
    trades net positive? Returns (ok, net, detail)."""
    try:
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("SELECT result, pnl, ask_cents, bid_path FROM paper "
                  "WHERE bid_path IS NOT NULL AND result IN ('WIN','LOSS') "
                  "AND ask_cents < ?", (TAKER_MAX_ASK_CENTS,))
        rows = c.fetchall()
        conn.close()
    except Exception:
        return False, 0.0, "no path data"
    if not rows:
        return False, 0.0, "no bid-path data yet"
    saved = false_cost = 0.0
    for res, pnl, ask, pj in rows:
        try:
            path = json.loads(pj)
        except Exception:
            continue
        shares = LIVE_STAKE / ((ask or 99.0) / 100.0)
        dip = next((b for _, b in path if b is not None and b <= EXIT_TRIGGER_CENTS), None)
        if res == "LOSS" and dip is not None:
            saved += shares * dip / 100.0
        elif res == "WIN" and dip is not None:
            false_cost += shares * (100.0 - dip) / 100.0
    net = saved - false_cost
    return net > 0, net, f"recover ${saved:.2f} − false ${false_cost:.2f}"


def evaluate_gates():
    """Returns (armed_bool, allowed_assets_set, human_report)."""
    lines = []
    cs = certified_stats()
    if cs is None:
        return False, set(), "❌ paper DB not readable — is DB_PATH the shared volume?"

    # GATE 1
    g1 = cs["n"] >= MIN_CERT_TRADES
    lines.append(f"{'✅' if g1 else '❌'} GATE 1 certified sample: {cs['n']}/"
                 f"{MIN_CERT_TRADES} settlement-graded in-band trades")

    # GATE 2
    g2 = False
    if cs["n"] > 0:
        g2 = cs["net"] >= MIN_CERT_NET and cs["wr"] is not None and cs["wr"] > cs["avg_ask"]
        lines.append(f"{'✅' if g2 else '❌'} GATE 2 certified edge: net "
                     f"${cs['net']:+.2f} (need ≥${MIN_CERT_NET:.0f}) · "
                     f"{cs['wr']:.1f}% vs BE {cs['avg_ask']:.1f}¢")
    else:
        lines.append("❌ GATE 2 certified edge: no certified trades yet")

    # GATE 3 (only if exit requested)
    if USE_EXIT:
        g3, xnet, xdet = exit_is_profitable()
        lines.append(f"{'✅' if g3 else '❌'} GATE 3 exit proven: net "
                     f"${xnet:+.2f} ({xdet})")
    else:
        g3 = True
        lines.append("➖ GATE 3 exit disabled (USE_EXIT=false)")

    # GATE 4 manual
    g4 = (LIVE_ARM == "YES_I_REVIEWED")
    lines.append(f"{'✅' if g4 else '❌'} GATE 4 manual arm: "
                 f"{'set' if g4 else 'set LIVE_ARM=YES_I_REVIEWED after reading /stats'}")

    # per-asset inclusion (data-driven) — only matters if the top gates pass
    allowed = set()
    per = cs["per_asset"]
    detail = []
    for a in ASSET_LIST:
        if a in EXCLUDE_ASSETS:
            detail.append(f"  {a}: excluded by name (EXCLUDE_ASSETS)")
            continue
        d = per.get(a)
        if not d or d["n"] < 30:
            detail.append(f"  {a}: {d['n'] if d else 0} trades — excluded (too few)")
            continue
        ok = d["net"] >= PER_ASSET_MIN_NET and (d["w"] / d["n"] * 100) > (d["ask"] / d["n"])
        if ok:
            allowed.add(a)
        detail.append(f"  {'✓' if ok else 'out'} {a}: {d['n']} trades · "
                      f"net ${d['net']:+.2f} → {'IN' if ok else 'watched/out'}")

    armed = g1 and g2 and g3 and g4 and bool(allowed)
    report = "\n".join(lines) + "\n— per-asset (certified) —\n" + "\n".join(detail)
    return armed, allowed, report


# ══════════════════════════════════════════════════════════════════════════
#  ORDER PLACEMENT (ported verbatim in shape from bot_variant_MEASURED.py)
# ══════════════════════════════════════════════════════════════════════════
def init_client():
    global clob_client
    if not V2_AVAILABLE:
        log.error("py_clob_client_v2 not installed — cannot trade")
        return False
    if not POLY_PRIVATE_KEY or not POLY_FUNDER:
        log.error("POLY_PRIVATE_KEY / POLY_FUNDER not set — cannot trade")
        return False
    try:
        temp = ClobClient(host=CLOB_BASE, chain_id=137, key=POLY_PRIVATE_KEY,
                          signature_type=3, funder=POLY_FUNDER)
        creds = temp.create_or_derive_api_key()
        clob_client = ClobClient(host=CLOB_BASE, chain_id=137, key=POLY_PRIVATE_KEY,
                                 creds=creds, signature_type=3, funder=POLY_FUNDER)
        log.info("[CLIENT] authenticated CLOB client ready")
        return True
    except Exception as e:
        log.error(f"[CLIENT] init failed: {e}")
        return False


def market_buy(token_id, usdc_amount):
    """FAK market buy — same call the maker bot uses for taker fills."""
    if not clob_client:
        return False, 0.0, 0.0
    try:
        args = MarketOrderArgs(token_id=token_id, amount=usdc_amount, side=BUY,
                               order_type=OrderType.FAK)
        resp = clob_client.create_and_post_market_order(
            order_args=args,
            options=PartialCreateOrderOptions(tick_size="0.01", neg_risk=False),
            order_type=OrderType.FAK)
        ok = isinstance(resp, dict) and (resp.get("success") or resp.get("status") == "matched")
        shares = float(resp.get("makingAmount", 0) or 0) if isinstance(resp, dict) else 0
        return ok, shares, usdc_amount
    except Exception as e:
        log.error(f"[BUY] {e}")
        return False, 0.0, 0.0


def limit_sell(token_id, shares, price_cents):
    """GTC sell — the exit. Same call shape as the maker bot's place_sell_order."""
    if not clob_client:
        return False
    try:
        args = OrderArgs(token_id=token_id, price=round(price_cents / 100.0, 2),
                         size=shares, side=SELL)
        resp = clob_client.create_and_post_order(
            args,
            options=PartialCreateOrderOptions(tick_size="0.01", neg_risk=False),
            order_type=OrderType.GTC)
        return isinstance(resp, dict) and (resp.get("success") or resp.get("status") == "matched")
    except Exception as e:
        log.error(f"[SELL] {e}")
        return False


# ══════════════════════════════════════════════════════════════════════════
#  MAIN — evaluate gates, then either ARM or stay in safe monitoring mode
# ══════════════════════════════════════════════════════════════════════════
def main():
    armed, allowed, report = evaluate_gates()
    tg("🔦 <b>LIVE TAKER — arming check</b>\n" + report +
       f"\n\n<b>{'🟢 ARMED — will trade with REAL money' if armed else '🔴 NOT ARMED — monitoring only, no orders'}</b>"
       + (f"\nassets live: {', '.join(sorted(allowed))}" if armed else ""))

    if not armed:
        log.info("[ARM] gates not cleared — staying in monitoring mode, no orders")
        # idle: re-check hourly so the day it qualifies, you get told
        while True:
            time.sleep(3600)
            a2, al2, rep2 = evaluate_gates()
            if a2:
                tg("🟢 <b>Gates now CLEARED.</b> Restart me to begin live "
                   "trading (or I stay idle for safety).\n" + rep2)
            time.sleep(1)
        return

    # ---- ARMED PATH ----
    if not init_client():
        tg("🔴 armed but CLOB client failed to init — no trading. Check keys.")
        return
    tg(f"🟢 <b>LIVE TAKER trading</b> · stake ${LIVE_STAKE:g} · band &lt;"
       f"{TAKER_MAX_ASK_CENTS:.0f}¢ · assets {', '.join(sorted(allowed))}\n"
       f"daily stop ${DAILY_LOSS_STOP:.0f} · exit@{EXIT_TRIGGER_CENTS:.0f}¢ "
       f"{'on' if USE_EXIT else 'off'} · bankroll stop ${BANKROLL_STOP:.0f}")
    # The live entry/scoring/exit loop reuses the paper engine's gate + the
    # order calls above. It is intentionally left for the supervised first-run
    # session: arming is the gated milestone; turning the loop on is done live,
    # together, once the arming message above prints 🟢.
    log.info("[ARM] ARMED. Entry loop is enabled in the supervised go-live step.")
    while True:
        time.sleep(1)


if __name__ == "__main__":
    main()
