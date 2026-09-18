#!/usr/bin/env python3
# PAPER FAVORITE-DIP LADDER — buys dips on the FAVORITE side, ladders out as it
# recovers (no money)
#
# THE IDEA
#   The longshot ladder banked money by selling into spikes on CHEAP (1-5c)
#   longshots — but those books are thin, so live fills diverged from paper
#   (share-count mismatches, stalled rungs, missed spikes on 3s polling).
#   This applies the SAME banking mechanic to the FAVORITE side instead: when
#   a side that's clearly become the favorite (ask has traded well above 50c)
#   dips DOWN by a defined amount, buy the dip; as it climbs back toward $1,
#   sell fixed-cent increments on the way, banking profit. The bet: favorites
#   dip and recover constantly, and 60-95c books are deep, so fills should be
#   clean — no slippage, no stuck rungs, no missed spikes.
#
# HOW THIS DIFFERS FROM THE LONGSHOT LADDER
#   - Entry is a DIP on an established favorite, not a cheap buy near the open
#   - Entry can fire ANY TIME in the window, not just the first N seconds
#   - Ladder rungs are ADDITIVE (fixed-cent steps) — a 74c position can't
#     double, it's capped near the exchange's own 99c ceiling
#   - No stop-loss on further drops, on purpose: this project's measured
#     finding is that early exits mostly sell positions that would have
#     recovered (both the bid-trigger and spot-reversal exits were ruled out
#     by live data). If the dip keeps falling, it rides to settlement.
#
# HONEST LIMITS
#   - UNTESTED. No paper data exists yet for this mechanic — this run IS the
#     test. Do not draw conclusions before ~100+ settled trades.
#   - Per-trade payout is small (you're buying something already likely to
#     win) — a run of bad reversals can outweigh many small dip-buys. This
#     can't be rescued by one lucky longshot the way the old ladder could.
#   - FAVORITE_MIN_CENTS / DIP_DROP_CENTS / RUNG_STEP_CENTS below are starting
#     guesses, not measured optima. Tune them AFTER real data exists, not
#     before — and one change at a time, same discipline as every other bot.
#   - Feed-fallback settlement grading carries the same ~0.5% fog as every
#     other bot in this project.
#
# ENV (required): TELEGRAM_TOKEN, TELEGRAM_CHAT_ID
# ENV (optional): PAPER_STAKE=5, TIMEFRAMES=15,60,240, FAVORITE_MIN_CENTS=65,
#   DIP_DROP_CENTS=10, DIP_FLOOR_CENTS=50, ENTRY_CUTOFF_SECS=30, MAX_STACK=1,
#   RUNG_STEP_CENTS=8, LADDER_SELL_FRAC=0.5, RUNG_CAP_CENTS=99,
#   MONITOR_POLL_SECS=2, SETTLE_POLL_SECS=15, SETTLE_TIMEOUT_SECS=1800,
#   DB_PATH=paper_favorite_dip.db, SEND_EACH=true

import os, time, json, sqlite3, logging, threading, requests
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
try:
    import websocket
    WEBSOCKET_AVAILABLE = True
except ImportError:
    WEBSOCKET_AVAILABLE = False

TELEGRAM_TOKEN   = os.environ["TELEGRAM_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
PAPER_STAKE      = float(os.environ.get("PAPER_STAKE", "5"))
DB_PATH          = os.environ.get("DB_PATH", "paper_favorite_dip.db")
SEND_EACH        = os.environ.get("SEND_EACH", "true").lower() == "true"

# 5m excluded by default — too little runway for a dip to recover and ladder.
TFS = [int(x) for x in os.environ.get("TIMEFRAMES", "15,60,240").split(",")]

# ── ENTRY: dip on an established favorite ───────────────────────────────────
FAVORITE_MIN_CENTS = float(os.environ.get("FAVORITE_MIN_CENTS", "65"))
DIP_DROP_CENTS     = float(os.environ.get("DIP_DROP_CENTS", "10"))
DIP_FLOOR_CENTS    = float(os.environ.get("DIP_FLOOR_CENTS", "50"))
ENTRY_CUTOFF_SECS  = float(os.environ.get("ENTRY_CUTOFF_SECS", "30"))
MAX_STACK          = int(os.environ.get("MAX_STACK", "1"))

# ── LADDER: sell a fixed-cent increment each time the bid climbs a rung ────
RUNG_STEP_CENTS  = float(os.environ.get("RUNG_STEP_CENTS", "8"))
LADDER_SELL_FRAC = float(os.environ.get("LADDER_SELL_FRAC", "0.5"))
# Polymarket's own order price ceiling is 99c (confirmed elsewhere in this
# project — buys above 0.99 get rejected live). Rungs never climb past it;
# once the bid reaches it, the whole remainder sells rather than dangling.
RUNG_CAP_CENTS   = float(os.environ.get("RUNG_CAP_CENTS", "99"))

MONITOR_POLL_SECS   = float(os.environ.get("MONITOR_POLL_SECS", "2"))
SETTLE_POLL_SECS    = float(os.environ.get("SETTLE_POLL_SECS", "15"))
SETTLE_TIMEOUT_SECS = float(os.environ.get("SETTLE_TIMEOUT_SECS", "1800"))

ASSET_LIST = ["BTC", "ETH", "SOL", "DOGE", "BNB", "XRP", "HYPE"]
ASSET_EMOJI = {"BTC": "🟠", "ETH": "🔷", "SOL": "🟣", "DOGE": "🟡",
               "BNB": "🟨", "XRP": "⚪", "HYPE": "🟢"}
ASSET_FULLNAME = {"BTC": "bitcoin", "ETH": "ethereum", "SOL": "solana",
                  "DOGE": "dogecoin", "BNB": "bnb", "XRP": "xrp", "HYPE": "hype"}
CLOB_BASE = "https://clob.polymarket.com"
GAMMA_BASE = "https://gamma-api.polymarket.com"
ET = ZoneInfo("America/New_York")
BINANCE_WS = ("wss://data-stream.binance.vision/stream?streams=" +
              "/".join(f"{s}usdt@bookTicker" for s in
                       ["btc", "eth", "sol", "doge", "bnb", "xrp"]))
BINANCE_SYM_TO_ASSET = {f"{s.upper()}USDT": s.upper()
                        for s in ["btc", "eth", "sol", "doge", "bnb", "xrp"]}

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("paper-favorite-dip")

prices_ref = {}
ref_last = {}


def money(x):
    """+$2.10 / −$5.00 — sign before the dollar, always two decimals."""
    return f"{'+' if x >= 0 else chr(0x2212)}${abs(x):.2f}"


def label_for(tf):
    return "4h" if tf == 240 else "1h" if tf == 60 else f"{tf}m"


def binance_ref_worker():
    while True:
        ws = None
        try:
            ws = websocket.create_connection(BINANCE_WS, timeout=10)
            ws.settimeout(30)
            log.info("[REF] Binance.vision reference feed connected")
            while True:
                msg = ws.recv()
                if not msg:
                    continue
                d = json.loads(msg).get("data", {})
                a = BINANCE_SYM_TO_ASSET.get(d.get("s"))
                if a:
                    b, k = float(d.get("b", 0)), float(d.get("a", 0))
                    if b > 0 and k > 0:
                        prices_ref[a] = (b + k) / 2.0
                        ref_last[a] = time.time()
        except Exception as e:
            log.warning(f"[REF] error: {e} — reconnecting")
        finally:
            try:
                ws and ws.close()
            except Exception:
                pass
        time.sleep(3)


def window_times(tf):
    now = time.time()
    if tf == 60:
        now_et = datetime.now(timezone.utc).astimezone(ET)
        start_et = now_et.replace(minute=0, second=0, microsecond=0)
        o = int(start_et.timestamp())
        return o, o + 3600, o + 3600 - now
    if tf == 240:
        now_et = datetime.now(timezone.utc).astimezone(ET)
        block_hour = (now_et.hour // 4) * 4
        start_et = now_et.replace(hour=block_hour, minute=0, second=0, microsecond=0)
        o = int(start_et.timestamp())
        return o, o + 14400, o + 14400 - now
    L = tf * 60
    o = int(now // L) * L
    return o, o + L, o + L - now


def build_slug(asset, tf, open_ts):
    if tf == 240:
        return f"{asset.lower()}-updown-4h-{open_ts}"
    if tf == 60:
        dt_et = datetime.fromtimestamp(open_ts, tz=ET)
        month = dt_et.strftime("%B").lower()
        day = dt_et.day
        year = dt_et.year
        hour12 = dt_et.strftime("%I").lstrip("0") or "12"
        ampm = dt_et.strftime("%p").lower()
        return f"{ASSET_FULLNAME[asset]}-up-or-down-{month}-{day}-{year}-{hour12}{ampm}-et"
    return f"{asset.lower()}-updown-{tf}m-{open_ts}"


_market_cache = {}

def resolve_tokens(asset, tf, open_ts):
    key = (asset, tf, open_ts)
    if key in _market_cache:
        return _market_cache[key]
    slug = build_slug(asset, tf, open_ts)
    try:
        r = requests.get(f"{GAMMA_BASE}/events", params={"slug": slug}, timeout=8)
        arr = r.json()
        ev = arr[0] if isinstance(arr, list) and arr else arr
        markets = ev.get("markets", []) if isinstance(ev, dict) else []
        if markets:
            toks = json.loads(markets[0].get("clobTokenIds", "[]"))
            if len(toks) == 2:
                _market_cache[key] = (toks[0], toks[1])
                return _market_cache[key]
    except Exception as e:
        log.debug(f"[RESOLVE] {slug}: {e}")
    _market_cache[key] = None
    return None


def best_ask_cents(token_id):
    try:
        r = requests.get(f"{CLOB_BASE}/book", params={"token_id": token_id}, timeout=6)
        b = r.json()
        prices = [float(a["price"]) for a in b.get("asks", [])
                  if float(a.get("size", 0)) > 0]
        return min(prices) * 100.0 if prices else None
    except Exception:
        return None


def best_bid_cents(token_id):
    try:
        r = requests.get(f"{CLOB_BASE}/book", params={"token_id": token_id}, timeout=6)
        b = r.json()
        prices = [float(x["price"]) for x in b.get("bids", [])
                  if float(x.get("size", 0)) > 0]
        return max(prices) * 100.0 if prices else None
    except Exception:
        return None


def fetch_polymarket_outcome(asset, tf, open_ts):
    slug = build_slug(asset, tf, open_ts)
    try:
        r = requests.get(f"{GAMMA_BASE}/events", params={"slug": slug}, timeout=10)
        data = r.json()
        if not data or not isinstance(data, list):
            return None
        markets = data[0].get("markets", [])
        if not markets:
            return None
        op = markets[0].get("outcomePrices")
        if isinstance(op, str):
            try:
                op = json.loads(op)
            except Exception:
                pass
        if not op or len(op) < 2:
            return None
        up_p, down_p = float(op[0]), float(op[1])
        if up_p >= 0.99:
            return "UP"
        if down_p >= 0.99:
            return "DOWN"
        return None
    except Exception as e:
        log.warning(f"[OUTCOME] {slug}: {e}")
        return None


def init_db():
    conn = sqlite3.connect(DB_PATH)
    conn.execute("""CREATE TABLE IF NOT EXISTS trades (
        id INTEGER PRIMARY KEY AUTOINCREMENT, created TEXT, asset TEXT, tf INTEGER,
        direction TEXT, open_ts INTEGER, close_ts INTEGER, entry_ask REAL,
        peak_at_entry REAL, result TEXT, pnl REAL, ladder_sold REAL DEFAULT 0,
        ladder_proceeds REAL DEFAULT 0, hold_pnl REAL)""")
    conn.execute("UPDATE trades SET result='VOID' WHERE result='PENDING'")
    conn.commit()
    conn.close()


def db_insert(asset, tf, direction, open_ts, close_ts, entry_ask, peak_at_entry):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("""INSERT INTO trades (created,asset,tf,direction,open_ts,close_ts,
                 entry_ask,peak_at_entry,result) VALUES (?,?,?,?,?,?,?,?, 'PENDING')""",
              (datetime.now(timezone.utc).isoformat(), asset, tf, direction,
               open_ts, close_ts, entry_ask, peak_at_entry))
    rid = c.lastrowid
    conn.commit()
    conn.close()
    return rid


def db_resolve(rid, result, pnl, ladder_sold, ladder_proceeds, hold_pnl):
    conn = sqlite3.connect(DB_PATH)
    conn.execute("""UPDATE trades SET result=?, pnl=?, ladder_sold=?,
                    ladder_proceeds=?, hold_pnl=? WHERE id=?""",
                 (result, pnl, ladder_sold, ladder_proceeds, hold_pnl, rid))
    conn.commit()
    conn.close()


def db_scoreboard():
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT result, pnl, tf FROM trades WHERE result IN ('WIN','LOSS')")
    rows = c.fetchall()
    conn.close()
    wins = sum(1 for r in rows if r[0] == "WIN")
    pnl = sum(r[1] or 0 for r in rows)
    wr = (wins / len(rows) * 100) if rows else None
    by_tf = {}
    for r in rows:
        d = by_tf.setdefault(r[2], {"n": 0, "w": 0, "pnl": 0.0})
        d["n"] += 1
        d["w"] += 1 if r[0] == "WIN" else 0
        d["pnl"] += r[1] or 0
    return {"n": len(rows), "wins": wins, "wr": wr, "pnl": pnl, "by_tf": by_tf}


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


_upd = None

def handle_commands():
    global _upd
    try:
        p = {"timeout": 1}
        if _upd:
            p["offset"] = _upd
        for u in requests.get(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates",
                              params=p, timeout=5).json().get("result", []):
            _upd = u["update_id"] + 1
            t = u.get("message", {}).get("text", "").strip().lower()
            if str(u.get("message", {}).get("chat", {}).get("id")) != str(TELEGRAM_CHAT_ID):
                continue
            if t == "/stats":
                sb = db_scoreboard()
                if sb["n"] == 0:
                    tg("📊 <b>FAVORITE DIP · PAPER</b>\nno settled trades yet")
                    continue
                tf_bits = [f"{label_for(tf)} {money(d['pnl'])}"
                          for tf, d in sorted(sb["by_tf"].items())]
                tg(f"📊 <b>FAVORITE DIP · PAPER</b>\n"
                   f"{sb['n']} trades · {sb['wr']:.1f}% win\n"
                   f"{' · '.join(tf_bits)}\n"
                   f"━━━━━━━━━━\nP&L <b>{money(sb['pnl'])}</b>")
            elif t == "/status":
                with pending_lock:
                    snap = [dict(asset=p["asset"], tf=p["tf"], direction=p["direction"],
                                 entry=p["entry_ask"], banked=p["ladder_proceeds"],
                                 left=p["shares_left"], rung=p["next_rung"],
                                 peak_after=p.get("peak_bid", 0.0))
                            for p in pending]
                head = f"📊 <b>FAVORITE DIP status</b>\n{len(snap)} open"
                lines = []
                for p in snap:
                    ar = "↑" if p["direction"] == "UP" else "↓"
                    st = (f"banked ${p['banked']:.2f}" if p["banked"] > 0
                          else "no rungs yet")
                    pk = f" · peak {p['peak_after']:.0f}¢" if p["peak_after"] else ""
                    lines.append(f"{ASSET_EMOJI.get(p['asset'],'')}{p['asset']} "
                                 f"{label_for(p['tf'])} {ar} @{p['entry']:.0f}¢\n"
                                 f"  {st} · {p['left']:.0f} riding · "
                                 f"next {p['rung']:.0f}¢{pk}")
                tg(head + ("\n\n" + "\n".join(lines) if lines else "\n\nno open positions"))
            elif t == "/help":
                tg("📖 <b>commands</b>\n/stats — scoreboard\n"
                   "/status — open positions\n/help — this list")
    except Exception:
        pass


# (asset,tf,open_ts,direction) -> highest ask seen so far this window
peak_ask = {}
# (asset,tf,open_ts,direction) already entered this window
fired = set()
# ("REF",tf,open_ts) -> {asset: underlying ref price at window start},
# captured ONLY for settlement-fallback grading — never used for entry
open_windows = {}
pending = []
pending_lock = threading.Lock()


def _cleanup_stale(now):
    cutoff = now - 5 * 3600   # generous buffer past the longest (4h) window
    for k in [k for k in peak_ask if k[2] < cutoff]:
        del peak_ask[k]
    for k in [k for k in open_windows if k[2] < cutoff]:
        del open_windows[k]
    fired.difference_update([k for k in fired if k[2] < cutoff])


def dip_monitor():
    """Every MONITOR_POLL_SECS: track each side's peak ask, fire a dip-entry
    when conditions are met, and ladder-sell any open position whose bid has
    climbed to the next rung. Dip detection doesn't need the longshot bot's
    fast 0.5s cadence — favorites dip on their own schedule, not in a narrow
    entry window at window-open."""
    last_cleanup = 0.0
    while True:
        try:
            time.sleep(MONITOR_POLL_SECS)
            now = time.time()
            if now - last_cleanup > 900:
                _cleanup_stale(now)
                last_cleanup = now

            for tf in TFS:
                open_ts, close_ts, secs_left = window_times(tf)
                ref_key = ("REF", tf, open_ts)
                if ref_key not in open_windows:
                    open_windows[ref_key] = dict(prices_ref)
                if secs_left < ENTRY_CUTOFF_SECS:
                    continue
                for asset in ASSET_LIST:
                    toks = resolve_tokens(asset, tf, open_ts)
                    if not toks:
                        continue
                    for direction, tok in (("UP", toks[0]), ("DOWN", toks[1])):
                        key = (asset, tf, open_ts, direction)
                        ask = best_ask_cents(tok)
                        if ask is None:
                            continue
                        pk = peak_ask.get(key, 0.0)
                        if ask > pk:
                            peak_ask[key] = ask
                            pk = ask
                        if key in fired:
                            continue
                        if pk < FAVORITE_MIN_CENTS:
                            continue
                        if ask < DIP_FLOOR_CENTS:
                            continue
                        if pk - ask < DIP_DROP_CENTS:
                            continue
                        # ── ENTRY: dip on an established favorite ──
                        fired.add(key)
                        rid = db_insert(asset, tf, direction, open_ts, close_ts,
                                        ask, pk)
                        shares_total = PAPER_STAKE / (ask / 100.0)
                        with pending_lock:
                            pending.append({
                                "rid": rid, "asset": asset, "tf": tf,
                                "direction": direction, "open_ts": open_ts,
                                "close_ts": close_ts, "entry_ask": ask,
                                "peak_at_entry": pk, "token": tok,
                                "shares_total": shares_total,
                                "shares_left": shares_total,
                                "next_rung": min(ask + RUNG_STEP_CENTS, RUNG_CAP_CENTS),
                                "ladder_proceeds": 0.0, "ladder_sold": 0.0,
                                "peak_bid": ask,
                            })
                        if SEND_EACH:
                            arrow = "↑" if direction == "UP" else "↓"
                            tg(f"🔵 <b>{ASSET_EMOJI.get(asset,'')}{asset} "
                               f"{label_for(tf)} {arrow} (favorite)</b>"
                               f" — ${PAPER_STAKE:g} @ {ask:.0f}¢\n"
                               f"{shares_total:.0f} sh · dipped from {pk:.0f}¢ · "
                               f"win pays +${shares_total - PAPER_STAKE:.0f}")
                        log.info(f"[DIP] {asset} {tf} {direction} entered "
                                 f"{ask:.1f}c (peak {pk:.1f}c)")

            with pending_lock:
                items = list(pending)
            for s in items:
                if now >= s["close_ts"] or s["shares_left"] < 1:
                    continue
                bid = best_bid_cents(s["token"])
                if bid is None:
                    continue
                if bid > s.get("peak_bid", 0.0):
                    s["peak_bid"] = bid
                sold_this_poll = 0.0
                proceeds_this_poll = 0.0
                while bid >= s["next_rung"] and s["shares_left"] >= 1:
                    at_cap = s["next_rung"] >= RUNG_CAP_CENTS
                    sell_shares = s["shares_left"] * LADDER_SELL_FRAC
                    if sell_shares < 1 or at_cap:
                        sell_shares = s["shares_left"]   # sweep dust / the cap
                    proceeds = sell_shares * (bid / 100.0)
                    s["ladder_proceeds"] += proceeds
                    s["ladder_sold"] += sell_shares
                    s["shares_left"] -= sell_shares
                    sold_this_poll += sell_shares
                    proceeds_this_poll += proceeds
                    if at_cap:
                        break
                    s["next_rung"] = min(s["next_rung"] + RUNG_STEP_CENTS,
                                         RUNG_CAP_CENTS)
                if sold_this_poll > 0:
                    tg(f"🪜 <b>{ASSET_EMOJI.get(s['asset'],'')}{s['asset']} "
                       f"{label_for(s['tf'])}</b> — sold {sold_this_poll:.0f} sh "
                       f"@ {bid:.0f}¢ → +${proceeds_this_poll:.2f}\n"
                       f"banked ${s['ladder_proceeds']:.2f} · "
                       f"{s['shares_left']:.0f} riding · "
                       f"next {s['next_rung']:.0f}¢")
                    log.info(f"[LADDER] {s['asset']} {s['tf']} sold "
                             f"{sold_this_poll:.1f} @ {bid:.0f}c banked "
                             f"${s['ladder_proceeds']:.2f} left "
                             f"{s['shares_left']:.1f}")
        except Exception as e:
            log.error(f"[MONITOR] {e}")


def scorer():
    while True:
        try:
            time.sleep(1.0)
            now = time.time()
            with pending_lock:
                items = list(pending)
            for s in items:
                if now < s["close_ts"] + 2:
                    continue
                if now - s.get("last_chk", 0) < SETTLE_POLL_SECS:
                    continue
                s["last_chk"] = now
                outcome = fetch_polymarket_outcome(s["asset"], s["tf"], s["open_ts"])
                graded_by = "settlement"
                if outcome is None:
                    if now <= s["close_ts"] + SETTLE_TIMEOUT_SECS:
                        continue
                    ow = open_windows.get(("REF", s["tf"], s["open_ts"]), {})
                    op = ow.get(s["asset"])
                    settle_px = prices_ref.get(s["asset"])
                    if op is None or settle_px is None or abs((settle_px - op) / op) < 1e-6:
                        db_resolve(s["rid"], "VOID", 0, s["ladder_sold"],
                                   s["ladder_proceeds"], 0)
                        with pending_lock:
                            s in pending and pending.remove(s)
                        continue
                    outcome = "UP" if settle_px > op else "DOWN"
                    graded_by = "feed-fallback"
                won = (s["direction"] == outcome)
                stake = PAPER_STAKE
                hold_pnl = (s["shares_total"] * 1.0 - stake) if won else -stake
                remaining_settle = (s["shares_left"] * 1.0) if won else 0.0
                pnl = round(s["ladder_proceeds"] + remaining_settle - stake, 4)
                result = "WIN" if won else "LOSS"
                db_resolve(s["rid"], result, pnl, s["ladder_sold"],
                           round(s["ladder_proceeds"], 4), round(hold_pnl, 4))
                with pending_lock:
                    s in pending and pending.remove(s)
                sb = db_scoreboard()
                tag = "" if graded_by == "settlement" else " ⚠️ feed-graded"
                lbl = label_for(s["tf"])
                em = ASSET_EMOJI.get(s["asset"], "")
                foot = f"━ {sb['n']} trades · {money(sb['pnl'])} total"
                ctx = f"entered {s['entry_ask']:.0f}¢ (dip from {s['peak_at_entry']:.0f}¢)"
                if won:
                    detail = (f"${s['ladder_proceeds']:.2f} banked + "
                              f"{s['shares_left']:.0f} sh paid out"
                              if s["ladder_proceeds"] > 0 else
                              f"{s['shares_left']:.0f} sh paid out")
                    tg(f"✅ <b>{em}{s['asset']} {lbl} WIN {money(pnl)}</b>{tag}\n"
                       f"{ctx}\n{detail}\n{foot}")
                elif pnl > 0:
                    tg(f"💰 <b>{em}{s['asset']} {lbl}</b> — settled against us, "
                       f"ladder banked it{tag}\n{ctx}\n"
                       f"net {money(pnl)} · (holding = {money(hold_pnl)})\n{foot}")
                elif s["ladder_sold"] > 0:
                    tg(f"❌ <b>{em}{s['asset']} {lbl}</b> — ladder softened it{tag}\n"
                       f"{ctx}\nbanked ${s['ladder_proceeds']:.2f} · "
                       f"net {money(pnl)} · (holding = {money(hold_pnl)})\n{foot}")
                else:
                    tg(f"❌ <b>{em}{s['asset']} {lbl}</b> — no rungs hit · "
                       f"{money(pnl)}{tag}\n{ctx}\n{foot}")
        except Exception as e:
            log.error(f"[SCORER] {e}")


def main():
    if not WEBSOCKET_AVAILABLE:
        log.error("websocket-client not installed")
        return
    init_db()
    threading.Thread(target=binance_ref_worker, daemon=True).start()
    labels = ", ".join(label_for(t) for t in TFS)
    tg(f"🔵 <b>FAVORITE DIP LADDER · PAPER</b> — no money, untested\n"
       f"buys dips ≥{DIP_DROP_CENTS:.0f}¢ below peak on sides that reached "
       f"≥{FAVORITE_MIN_CENTS:.0f}¢ · floor {DIP_FLOOR_CENTS:.0f}¢\n"
       f"ladder: sell {LADDER_SELL_FRAC:.0%} every {RUNG_STEP_CENTS:.0f}¢ climb\n"
       f"tf={labels} · stake ${PAPER_STAKE:g}\n/stats")
    threading.Thread(target=dip_monitor, daemon=True).start()
    threading.Thread(target=scorer, daemon=True).start()
    while True:
        try:
            handle_commands()
        except Exception as e:
            log.error(f"main: {e}")
        time.sleep(1)


if __name__ == "__main__":
    main()
