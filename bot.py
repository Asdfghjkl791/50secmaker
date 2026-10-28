#!/usr/bin/env python3
# LIVE BTC JUMP SNIPER (Oct 27 2026) - replaces the fav-dip bot in the 50secmaker service.
#
# THE RULE (from the paper jump logger; passed its fair test)
#   When BTC moves >= JUMP_BPS within JUMP_WINDOW seconds on Binance, look at the live BTC 5m and 15m
#   up/down markets. For the side the jump favours:
#     fair  = model chance that side wins (BTC vs the window's start price, BTC's recent volatility, time left)
#     edge  = fair - ask (ask read EDGE_DELAY seconds after the jump)
#   Trade when edge >= MIN_EDGE, ask < MAX_ASK, and (ask >= CHEAP_CENTS or edge >= CHEAP_EDGE), ask 5-95c.
#   Buy LIVE_STAKE dollars (fill-or-kill, never above ask + LIVE_MAX_OVERPAY_CENTS), sell HOLD_SECS later
#   (fill-or-kill, never below bid - LIVE_SELL_SLIP_CENTS; retries; if it still can't sell, it holds to the end).
#
# SAFETY
#   - OFF until LIVE_ENABLED=true. While off it runs the same logic on paper and messages every signal.
#   - Daily loss limit (LIVE_DAILY_LOSS_LIMIT, counts the worst case of anything still open), max trades per
#     hour, one position per market at a time. /stop pauses instantly, /go resumes.
#   - Every trade is shown next to what paper would have made, plus the real USDC balance change.
#
# COMMANDS: /status · /trades · /today · /balance · /stop · /go · /export · /help
#
# ENV (required): TELEGRAM_TOKEN, TELEGRAM_CHAT_ID, POLY_PRIVATE_KEY, POLY_FUNDER, POLY_SIG_TYPE
# ENV (optional): LIVE_ENABLED=false  LIVE_STAKE=5  LIVE_MAX_OVERPAY_CENTS=2  LIVE_SELL_SLIP_CENTS=2
#   LIVE_DAILY_LOSS_LIMIT=15  LIVE_MAX_TRADES_HOUR=20  HOLD_SECS=5  JL_TFS=5,15  JUMP_BPS=5  JUMP_WINDOW=2
#   JUMP_COOLDOWN=10  EDGE_DELAY=0.25  MIN_EDGE=10  MAX_ASK=85  CHEAP_CENTS=20  CHEAP_EDGE=15
#   DB_PATH=/data/live_jumper.db

import os, time, json, math, sqlite3, logging, threading, requests, csv, io, gzip, re
from collections import deque
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
import websocket

TELEGRAM_TOKEN = os.environ["TELEGRAM_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
DB_PATH = os.environ.get("DB_PATH", "live_jumper.db")
env_f = lambda k, d: float(os.environ.get(k, d))
LIVE_ENABLED = os.environ.get("LIVE_ENABLED", "false").strip().lower() == "true"
LIVE_STAKE = env_f("LIVE_STAKE", "5")
LIVE_MAX_OVERPAY = env_f("LIVE_MAX_OVERPAY_CENTS", "2")
LIVE_SELL_SLIP = env_f("LIVE_SELL_SLIP_CENTS", "2")
LIVE_DAILY_LOSS = env_f("LIVE_DAILY_LOSS_LIMIT", "15")
LIVE_MAX_TRADES_HOUR = int(env_f("LIVE_MAX_TRADES_HOUR", "20"))
HOLD_SECS = env_f("HOLD_SECS", "5")
TFS = [int(x) for x in os.environ.get("JL_TFS", "5,15").split(",") if x.strip()]
JUMP_BPS = env_f("JUMP_BPS", "5")
JUMP_WINDOW = env_f("JUMP_WINDOW", "2")
JUMP_COOLDOWN = env_f("JUMP_COOLDOWN", "10")
EDGE_DELAY = env_f("EDGE_DELAY", "0")            # decide on the book at the jump itself (fastest)
KEEP_EDGE = env_f("KEEP_EDGE_CENTS", "8")          # smart cap: may pay up to fair - 8c ...
SMART_MAX = env_f("SMART_MAX_OVERPAY_CENTS", "8")  # ... but never more than ask + 8c
MIN_EDGE = env_f("MIN_EDGE", "10")
MAX_ASK = env_f("MAX_ASK", "85")
CHEAP_CENTS = env_f("CHEAP_CENTS", "20")
CHEAP_EDGE = env_f("CHEAP_EDGE", "15")
POLY_PRIVATE_KEY = os.environ.get("POLY_PRIVATE_KEY", "").strip()
POLY_FUNDER = os.environ.get("POLY_FUNDER", "").strip()
POLY_SIG_TYPE = int(os.environ.get("POLY_SIG_TYPE", "1"))
FEE_RATE = 0.07
ASSET = "BTC"
CLOB_BASE = "https://clob.polymarket.com"
GAMMA = "https://gamma-api.polymarket.com"
MARKET_WS = "wss://ws-subscriptions-clob.polymarket.com/ws/market"
BINANCE_WS = "wss://data-stream.binance.vision/stream?streams=btcusdt@bookTicker"
BINANCE_REST = "https://data-api.binance.vision/api/v3/klines"
ET = ZoneInfo("America/New_York")
TZ = ZoneInfo("America/Toronto")

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("live-jumper")

lock = threading.RLock()          # books / markets
jlock = threading.Lock()          # price state
db_lock = threading.Lock()
trade_lock = threading.Lock()     # one live order at a time
books = {}                        # token -> {"bids": {c: sz}, "asks": {c: sz}}
markets = {}                      # (tf, open_ts) -> (up_tok, dn_tok)
opens = {}                        # (tf, open_ts) -> window start price
busy = set()                      # (tf, open_ts) with an open position
price = {"px": None, "ts": 0.0}
ticks = deque(maxlen=5000)        # (ts, px), last JUMP_WINDOW seconds
px1s = deque(maxlen=1200)         # (ts, px) ~1/s
state = {"last_jump": 0.0, "jumps": 0, "signals": 0, "started": time.time(), "bn": 0, "pm": 0, "err": ""}
_clob = None


def fee(sh, p):
    return sh * FEE_RATE * p * (1 - p)


def money(x):
    return f"{'+' if x >= 0 else chr(0x2212)}${abs(x):.2f}"


# ── database ────────────────────────────────────────────────────────────────
def db():
    c = sqlite3.connect(DB_PATH, timeout=30)
    c.row_factory = sqlite3.Row
    return c


def init_db():
    with db_lock:
        c = db()
        c.execute("""CREATE TABLE IF NOT EXISTS lj_trades (id INTEGER PRIMARY KEY AUTOINCREMENT, t0 REAL, tf INTEGER,
            open_ts INTEGER, side TEXT, bps REAL, fair REAL, ask REAL, bid0 REAL, edge REAL, mode TEXT, status TEXT,
            buy_cost REAL, buy_shares REAL, buy_px REAL, buy_ts REAL, sell_proceeds REAL, sell_shares REAL,
            sell_px REAL, sell_ts REAL, paper_bid REAL, paper_pnl REAL, pnl REAL, bal_before REAL, bal_after REAL,
            result TEXT, note TEXT)""")
        c.execute("CREATE TABLE IF NOT EXISTS lj_kv (k TEXT PRIMARY KEY, v TEXT)")
        c.commit()
        c.close()


def db_exec(sql, args=()):
    with db_lock:
        c = db()
        cur = c.execute(sql, args)
        c.commit()
        rid = cur.lastrowid
        c.close()
        return rid


def db_query(sql, args=()):
    with db_lock:
        c = db()
        r = c.execute(sql, args).fetchall()
        c.close()
        return r


def kv_get(k, d=None):
    r = db_query("SELECT v FROM lj_kv WHERE k=?", (k,))
    return r[0]["v"] if r else d


def kv_set(k, v):
    db_exec("INSERT OR REPLACE INTO lj_kv (k, v) VALUES (?, ?)", (k, str(v)))


def paused():
    return kv_get("paused", "0") == "1"


# ── telegram ────────────────────────────────────────────────────────────────
def tg(msg):
    try:
        r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                          json={"chat_id": TELEGRAM_CHAT_ID, "text": msg[:4000], "parse_mode": "HTML"}, timeout=8)
        if r.status_code != 200:
            log.error(f"tg {r.status_code}: {r.text[:150]}")
            plain = re.sub(r"</?b>|</?i>", "", msg).replace("&lt;", "<").replace("&gt;", ">").replace("&amp;", "&")
            requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                          json={"chat_id": TELEGRAM_CHAT_ID, "text": plain[:4000]}, timeout=8)
    except Exception as e:
        log.error(f"tg: {e}")


def tg_document(name, data, caption=""):
    try:
        requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendDocument",
                      data={"chat_id": TELEGRAM_CHAT_ID, "caption": caption[:1000]},
                      files={"document": (name, data, "application/gzip")}, timeout=120)
    except Exception as e:
        tg(f"⚠️ upload failed: {e}")


# ── Polymarket client (same setup the fav-dip bot used on this account) ─────
def clob():
    global _clob
    if _clob is not None:
        return _clob
    if not POLY_PRIVATE_KEY:
        raise RuntimeError("POLY_PRIVATE_KEY is not set in Railway")
    if POLY_SIG_TYPE in (1, 2) and not POLY_FUNDER:
        raise RuntimeError("POLY_FUNDER (your Polymarket wallet address) is not set")
    from py_clob_client_v2 import ClobClient
    c = ClobClient(CLOB_BASE, chain_id=137, key=POLY_PRIVATE_KEY, signature_type=POLY_SIG_TYPE,
                   funder=POLY_FUNDER or None)
    c.set_api_creds(c.create_or_derive_api_key())
    _clob = c
    log.info("[LIVE] connected")
    return c


def usdc_balance():
    from py_clob_client_v2 import BalanceAllowanceParams, AssetType
    r = clob().get_balance_allowance(BalanceAllowanceParams(asset_type=AssetType.COLLATERAL,
                                                             signature_type=POLY_SIG_TYPE))
    return float(r.get("balance", 0)) / 1e6


def token_balance(token):
    from py_clob_client_v2 import BalanceAllowanceParams, AssetType
    p = BalanceAllowanceParams(asset_type=AssetType.CONDITIONAL, token_id=token, signature_type=POLY_SIG_TYPE)
    try:
        clob().update_balance_allowance(p)
    except Exception:
        pass
    r = clob().get_balance_allowance(p)
    return float(r.get("balance", 0)) / 1e6


def _amounts(resp):
    try:
        return float(resp.get("makingAmount") or 0), float(resp.get("takingAmount") or 0)
    except Exception:
        return 0.0, 0.0


ORDER_TYPE = os.environ.get("ORDER_TYPE", "FAK").strip().upper()     # FAK = fill what you can, cancel the rest
warmed = set()
timing = {}                                                          # last order: build / post seconds


def warm(token):
    """Build (and sign) a throwaway order for a token WITHOUT sending it, so market info, fee info and the
    signing code are all loaded before a real trade needs them."""
    if not LIVE_ENABLED or token in warmed:
        return
    try:
        from py_clob_client_v2 import MarketOrderArgs, OrderType, Side
        t0 = time.time()
        clob().create_market_order(MarketOrderArgs(token_id=token, amount=1.0, side=Side.BUY, price=0.01,
                                                   order_type=OrderType.FOK))
        warmed.add(token)
        log.info(f"[LIVE] warmed {token[:10]}… in {time.time() - t0:.2f}s")
    except Exception as e:
        log.warning(f"[LIVE] warm {token[:10]}…: {e}")


def fast_post(c, order, ot):
    """Send a signed order and return Polymarket's answer straight away. (The library's post_order then keeps
    polling until the trade settles on-chain, which can take seconds and would push our 5-second sell later.)"""
    try:
        import py_clob_client_v2.client as cm
        owner = c.creds.api_key or ""
        payload = (cm.order_to_json_v2(order, owner, ot, False, False) if cm._is_v2_order(order)
                   else cm.order_to_json_v1(order, owner, ot, False, False))
        ser = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
        headers = c._l2_headers("POST", cm.POST_ORDER, body=payload, serialized_body=ser)
        return c._post(f"{c.host}{cm.POST_ORDER}", headers=headers, data=ser)
    except (AttributeError, ImportError, TypeError) as e:     # library changed: fall back to the normal call
        log.warning(f"[LIVE] fast_post fallback: {e}")
        return c.post_order(order, ot)


BATCH_ORDERS = os.environ.get("BATCH_ORDERS", "true").strip().lower() in ("1", "true", "yes", "on")


def build_order(token, side, amount, limit_c):
    from py_clob_client_v2 import MarketOrderArgs, OrderType, Side
    ot = OrderType.FAK if ORDER_TYPE == "FAK" else OrderType.FOK
    lim = max(0.01, min(0.99, round(limit_c / 100.0, 2)))
    mo = MarketOrderArgs(token_id=token, amount=round(amount, 2), side=Side.BUY if side == "BUY" else Side.SELL,
                         price=lim, order_type=ot)
    return clob().create_market_order(mo), ot


def check_resp(resp):
    """(ok, resp, note) from one order answer"""
    if not isinstance(resp, dict):
        resp = {"success": False, "errorMsg": str(resp)[:200]}
    if not resp.get("success", False) or resp.get("errorMsg"):
        return False, resp, str(resp.get("errorMsg") or resp)[:200]
    mk, tk = _amounts(resp)
    if str(resp.get("status", "")).lower() != "matched" and tk <= 0:
        return False, resp, f"status={resp.get('status')}"
    return True, resp, ""


def batch_post(c, items):
    """Send several signed orders in ONE request, so they all reach Polymarket together
    (sent one by one, the second waits ~0.4s behind the first). Returns one answer per order.
    Raises if the whole request fails."""
    import py_clob_client_v2.client as cm
    POST_ORDERS = getattr(cm, "POST_ORDERS", "/orders")
    owner = c.creds.api_key or ""
    payload = [cm.order_to_json_v2(o, owner, ot, False, False) if cm._is_v2_order(o)
               else cm.order_to_json_v1(o, owner, ot, False, False) for o, ot in items]
    ser = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
    headers = c._l2_headers("POST", POST_ORDERS, body=payload, serialized_body=ser)
    res = c._post(f"{c.host}{POST_ORDERS}", headers=headers, data=ser)
    if isinstance(res, dict) and isinstance(res.get("data"), list):
        res = res["data"]
    if not isinstance(res, list) or len(res) != len(items):
        raise RuntimeError(f"batch answer not understood: {str(res)[:150]}")
    return res


def market_order(token, side, amount, limit_c, tim=None):
    """Market order with a price limit. BUY: amount = dollars, limit = most we pay. SELL: amount = shares,
    limit = least we accept. FAK fills what it can at or better than the limit and cancels the rest.
    Returns (ok, resp, note)."""
    t0 = time.time()
    order, ot = build_order(token, side, amount, limit_c)
    t1 = time.time()
    try:
        resp = fast_post(clob(), order, ot) or {}
    except Exception as e:
        resp = {"success": False, "errorMsg": str(e)[:200]}
    t2 = time.time()
    if tim is not None:
        tim.update(build=t1 - t0, post=t2 - t1, sent=t1)
    log.info(f"[LIVE] {side} build {t1 - t0:.2f}s post {t2 - t1:.2f}s resp: {str(resp)[:300]}")
    return check_resp(resp)


# ── markets ─────────────────────────────────────────────────────────────────
def window(tf, now):
    L = tf * 60
    o = int(now // L) * L
    return o, o + L


def resolve(tf, open_ts):
    try:
        arr = requests.get(f"{GAMMA}/events", params={"slug": f"btc-updown-{tf}m-{open_ts}"}, timeout=8).json()
        ev = arr[0] if isinstance(arr, list) and arr else None
        mk = (ev or {}).get("markets", [])
        if mk:
            t = json.loads(mk[0].get("clobTokenIds", "[]"))
            if len(t) == 2:
                return str(t[0]), str(t[1])
    except Exception as e:
        log.debug(f"resolve {tf} {open_ts}: {e}")
    return None


def outcome(tf, open_ts):
    try:
        arr = requests.get(f"{GAMMA}/events", params={"slug": f"btc-updown-{tf}m-{open_ts}"}, timeout=10).json()
        mk = (arr[0] if isinstance(arr, list) and arr else {}).get("markets", [])
        op = mk[0].get("outcomePrices") if mk else None
        op = json.loads(op) if isinstance(op, str) else op
        if op and len(op) >= 2:
            if float(op[0]) >= 0.99:
                return "UP"
            if float(op[1]) >= 0.99:
                return "DOWN"
    except Exception as e:
        log.warning(f"outcome {tf} {open_ts}: {e}")
    return None


def kline_open(open_ts):
    try:
        j = requests.get(BINANCE_REST, params=dict(symbol="BTCUSDT", interval="1m", startTime=open_ts * 1000,
                                                   endTime=open_ts * 1000 + 59000, limit=1), timeout=8).json()
        if isinstance(j, list) and j:
            return float(j[0][1])
    except Exception as e:
        log.warning(f"kline {open_ts}: {e}")
    return None


def resolver_worker():
    while True:
        try:
            now = time.time()
            for tf in TFS:
                cur = window(tf, now)[0]
                if (tf, cur) not in opens and now >= cur + 60:
                    op = kline_open(cur)               # didn't see the open live: use Binance's 1m open
                    if op:
                        opens[(tf, cur)] = op
                for o in (cur, window(tf, now + 90)[0]):
                    if (tf, o) not in markets:
                        t = resolve(tf, o)
                        if t:
                            with lock:
                                markets[(tf, o)] = t
                            for tok in t:
                                warm(tok)
            with lock:
                for k in [k for k in markets if k[1] + k[0] * 60 < now - 600]:
                    for t in markets.pop(k):
                        books.pop(t, None)
            for k in [k for k in opens if k[1] + k[0] * 60 < now - 3600]:
                opens.pop(k, None)
        except Exception as e:
            state["err"] = f"resolver: {e}"
            log.error(state["err"])
        time.sleep(3)


# ── feeds ───────────────────────────────────────────────────────────────────
def pm_handle(raw):
    try:
        data = json.loads(raw)
    except Exception:
        return
    for m in (data if isinstance(data, list) else [data]):
        if not isinstance(m, dict):
            continue
        state["pm"] += 1
        et = m.get("event_type")
        with lock:
            if et == "book":
                tok = str(m.get("asset_id"))
                books[tok] = {"bids": {round(float(x["price"]) * 100, 3): float(x["size"]) for x in (m.get("bids") or m.get("buys") or [])},
                              "asks": {round(float(x["price"]) * 100, 3): float(x["size"]) for x in (m.get("asks") or m.get("sells") or [])}}
            elif et == "price_change":
                for ch in (m.get("price_changes") or m.get("changes") or []):
                    tok = str(ch.get("asset_id") or m.get("asset_id"))
                    b = books.setdefault(tok, {"bids": {}, "asks": {}})
                    lvl = b["bids"] if str(ch.get("side", "")).upper() == "BUY" else b["asks"]
                    px, sz = round(float(ch["price"]) * 100, 3), float(ch.get("size", 0))
                    if sz <= 0:
                        lvl.pop(px, None)
                    else:
                        lvl[px] = sz


def pm_worker():
    while True:
        try:
            with lock:
                toks = tuple(sorted(t for v in markets.values() for t in v))
            if not toks:
                time.sleep(2)
                continue
            stop = threading.Event()

            def on_open(ws):
                ws.send(json.dumps({"assets_ids": list(toks), "type": "market"}))

                def pinger():
                    while not stop.is_set():
                        time.sleep(10)
                        try:
                            ws.send("PING")
                        except Exception:
                            return
                threading.Thread(target=pinger, daemon=True).start()

            def on_message(ws, msg):
                if msg in ("PONG", "pong"):
                    return
                pm_handle(msg)
                with lock:
                    cur = tuple(sorted(t for v in markets.values() for t in v))
                if cur != toks:
                    ws.close()

            ws = websocket.WebSocketApp(MARKET_WS, on_open=on_open, on_message=on_message)
            ws.run_forever(ping_interval=20, ping_timeout=10)
            stop.set()
        except Exception as e:
            log.warning(f"pm ws: {e}")
        time.sleep(1)


def on_tick(now, px):
    with jlock:
        price["px"], price["ts"] = px, now
        if not px1s or now - px1s[-1][0] >= 1.0:
            px1s.append((now, px))
        ticks.append((now, px))
        while ticks and ticks[0][0] < now - JUMP_WINDOW:
            ticks.popleft()
        for tf in TFS:                                  # remember the price at each window's open (like the scanner)
            o = window(tf, now)[0]
            if (tf, o) not in opens and now - o <= 5:
                opens[(tf, o)] = px
        if now - state["last_jump"] < JUMP_COOLDOWN or len(ticks) < 2:
            return
        bps = (px / ticks[0][1] - 1) * 1e4
        if abs(bps) < JUMP_BPS:
            return
        state["last_jump"] = now
        state["jumps"] += 1
    threading.Thread(target=on_jump, args=(now, bps, px), daemon=True).start()


def bn_worker():
    while True:
        try:
            ws = websocket.create_connection(BINANCE_WS, timeout=10)
            ws.settimeout(30)
            log.info("binance connected")
            while True:
                d = json.loads(ws.recv()).get("data", {})
                b, a = float(d.get("b", 0)), float(d.get("a", 0))
                if b > 0 and a > 0:
                    state["bn"] += 1
                    on_tick(time.time(), (b + a) / 2)
        except Exception as e:
            log.warning(f"binance: {e}")
        time.sleep(3)


# ── model ───────────────────────────────────────────────────────────────────
def norm_cdf(z):
    return 0.5 * (1 + math.erf(z / math.sqrt(2)))


def sigma():
    pts = [p for p in list(px1s) if p[0] >= time.time() - 900]
    r = [(math.log(b / a)) ** 2 / (t1 - t0) for (t0, a), (t1, b) in zip(pts, pts[1:]) if t1 > t0 and a > 0 and b > 0]
    if len(r) < 30:
        return 6e-5
    return max(2e-5, math.sqrt(sum(r) / len(r)))


def fair_up(tf, o, now, px):
    op = opens.get((tf, o))
    left = o + tf * 60 - now
    if not op or not px or left <= 0:
        return None
    return 100.0 * norm_cdf(math.log(px / op) / (sigma() * math.sqrt(left)))


def best(tok, kind):
    with lock:
        b = books.get(tok)
        if not b or not b[kind]:
            return None
        return max(b[kind]) if kind == "bids" else min(b[kind])


# ── the trade ───────────────────────────────────────────────────────────────
def risk_check(pending=0):
    if paused():
        return "paused (/go to resume)"
    t_day = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    rows = db_query("SELECT pnl, buy_cost, status, t0 FROM lj_trades WHERE mode='LIVE' AND t0>=?", (t_day,))
    realized = sum(r["pnl"] or 0 for r in rows if r["pnl"] is not None)
    open_cost = sum(r["buy_cost"] or 0 for r in rows if r["pnl"] is None and r["status"] in ("BOUGHT", "HOLDING"))
    open_cost += LIVE_STAKE * pending
    if realized - open_cost - LIVE_STAKE < -LIVE_DAILY_LOSS - 1e-9:
        return f"daily loss limit ${LIVE_DAILY_LOSS:g} reached (today {money(realized)})"
    last_hour = sum(1 for r in rows if r["t0"] >= time.time() - 3600)
    if last_hour + pending >= LIVE_MAX_TRADES_HOUR:
        return f"{last_hour} live trades in the last hour (max {LIVE_MAX_TRADES_HOUR})"
    return None


def on_jump(t0, bps, px0):
    up = bps > 0
    fairs = {}
    with lock:
        live = [(k, v) for k, v in markets.items() if k[1] <= t0 < k[1] + k[0] * 60]
    for (tf, o), toks in live:
        f = fair_up(tf, o, t0, px0)
        if f is not None:
            fairs[(tf, o)] = (toks, f if up else 100 - f)
    time.sleep(max(0.0, t0 + EDGE_DELAY - time.time()))
    sigs = []
    for (tf, o), (toks, fair) in fairs.items():
        tok = toks[0] if up else toks[1]
        ask, bid = best(tok, "asks"), best(tok, "bids")
        if ask is None or bid is None or not (5 <= ask <= 95):
            continue
        edge = fair - ask
        if not (edge >= MIN_EDGE and ask < MAX_ASK and (ask >= CHEAP_CENTS or edge >= CHEAP_EDGE)):
            continue
        state["signals"] += 1
        sigs.append((t0, tf, o, tok, "UP" if up else "DOWN", bps, fair, ask, bid, edge))
    if not sigs:
        return
    if LIVE_ENABLED and BATCH_ORDERS and len(sigs) > 1:
        live_group(sigs)
        return
    for s in sigs:
        threading.Thread(target=trade, args=s, daemon=True).start()


def _head(tf, side, bps, fair, ask, edge):
    return f"{tf}m {side} {edge:+.0f}¢"


def short_why(note, cap):
    n = (note or "").lower()
    if "no orders found to match" in n or "not filled" in n or "status=" in n:
        return f"price ran past {cap:.0f}¢"
    if "not enough balance" in n or "allowance" in n:
        return "not enough USDC"
    return (note or "?")[:60]


def admit(t0, tf, o, tok, side, bps, fair, ask, bid, edge, mode, pending=0):
    """log the signal; for LIVE, check the limits and lock the market. Returns (rid, head, allowed)."""
    head = _head(tf, side, bps, fair, ask, edge)
    rid = db_exec("INSERT INTO lj_trades (t0,tf,open_ts,side,bps,fair,ask,bid0,edge,mode,status) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                  (t0, tf, o, side, bps, fair, ask, bid, edge, mode, "SIGNAL"))
    if mode != "LIVE":
        return rid, head, True
    with trade_lock:
        if (tf, o) in busy:
            db_exec("UPDATE lj_trades SET mode='SKIPPED', status='SKIPPED', note=? WHERE id=?", ("position already open", rid))
            return rid, head, False
        why = risk_check(pending)
        if why:
            db_exec("UPDATE lj_trades SET mode='BLOCKED', status='BLOCKED', note=? WHERE id=?", (why, rid))
            tg(f"⛔ {head} · skipped: {why}")
            return rid, head, False
        busy.add((tf, o))
    return rid, head, True


def buy_cap(ask, fair):
    return max(ask + LIVE_MAX_OVERPAY, min(ask + SMART_MAX, fair - KEEP_EDGE))


def live_group(sigs):
    """Two or more signals on the same jump: send all the buys in one request so none waits behind another."""
    acc = []
    for s in sigs:
        rid, head, ok = admit(*s, mode="LIVE", pending=len(acc))
        if ok:
            acc.append((s, rid, head))
    if not acc:
        return
    if len(acc) == 1:
        s, rid, head = acc[0]
        t0, tf, o, tok, side, bps, fair, ask, bid, edge = s
        _run_live(rid, head, tf, o, tok, side, ask, t0, fair)
        return
    tb = time.time()
    items, built = [], []
    for s, rid, head in acc:
        t0, tf, o, tok, side, bps, fair, ask, bid, edge = s
        cap = buy_cap(ask, fair)
        try:
            items.append(build_order(tok, "BUY", LIVE_STAKE, cap))
            built.append((s, rid, head, cap))
        except Exception as e:
            db_exec("UPDATE lj_trades SET mode='MISSED', status='MISSED', note=? WHERE id=?", (f"build: {str(e)[:150]}", rid))
            tg(f"⏭ {head} · order error: {str(e)[:60]}")
            busy.discard((tf, o))
    if not built:
        return
    t1 = time.time()
    try:
        resps, unsure = (batch_post(clob(), items) if len(items) > 1 else [fast_post(clob(), *items[0])]), False
    except Exception as e:
        resps, unsure = [{"success": False, "errorMsg": str(e)[:200]}] * len(items), True
    t2 = time.time()
    log.info(f"[LIVE] batch of {len(items)} build {t1 - tb:.2f}s post {t2 - t1:.2f}s resp: {str(resps)[:400]}")
    tim = {"build": t1 - tb, "post": t2 - t1, "sent": t1, "n": len(items)}
    for (s, rid, head, cap), r in zip(built, resps):
        t0, tf, o, tok, side, bps, fair, ask, bid, edge = s
        buy = (*check_resp(r), dict(tim), cap, unsure)
        threading.Thread(target=_run_live, args=(rid, head, tf, o, tok, side, ask, t0, fair, buy), daemon=True).start()


def _run_live(rid, head, tf, o, tok, side, ask, t0, fair, buy=None):
    try:
        live_round_trip(rid, head, tf, o, tok, side, ask, t0, fair, buy)
    finally:
        busy.discard((tf, o))


def trade(t0, tf, o, tok, side, bps, fair, ask, bid, edge):
    mode = "LIVE" if LIVE_ENABLED else "PAPER"
    rid, head, allowed = admit(t0, tf, o, tok, side, bps, fair, ask, bid, edge, mode)
    if not allowed:
        return
    if mode == "LIVE":
        try:
            live_round_trip(rid, head, tf, o, tok, side, ask, t0, fair)
        finally:
            busy.discard((tf, o))
    else:
        time.sleep(max(0.0, t0 + EDGE_DELAY + HOLD_SECS - time.time()))
        b = best(tok, "bids")
        st = LIVE_STAKE
        sh = st / (ask / 100)
        pp = None if b is None else sh * b / 100 - st - fee(sh, ask / 100) - fee(sh, b / 100)
        db_exec("UPDATE lj_trades SET status='PAPER', paper_bid=?, paper_pnl=?, pnl=? WHERE id=?", (b, pp, pp, rid))
        bs = "—" if b is None else f"{b:g}"
        tg(f"📝 {head} · {ask:g}→{bs}¢ · <b>{money(pp) if pp is not None else 'n/a'}</b>")


def held_shares(tf, o, side):
    return sum((r["buy_shares"] or 0) for r in db_query(
        "SELECT buy_shares FROM lj_trades WHERE status='HOLDING' AND tf=? AND open_ts=? AND side=?", (tf, o, side)))


def live_round_trip(rid, head, tf, o, tok, side, ask, t_jump=0.0, fair=0.0, buy=None):
    bal0 = state.get("bal")                      # cached balance (fetching it here would slow the buy down)
    unsure = False
    # BUY
    if buy is None:
        tim = {}
        cap = buy_cap(ask, fair)
        try:
            ok, resp, note = market_order(tok, "BUY", LIVE_STAKE, cap, tim)
        except Exception as e:
            ok, resp, note = False, {}, f"error: {str(e)[:150]}"
    else:
        ok, resp, note, tim, cap, unsure = buy
    lag = (f"{tim.get('sent', 0) + tim.get('post', 0) - t_jump:.2f}s"
           + (f" ×{tim['n']}" if tim.get("n", 1) > 1 else ""))
    lag_full = (f"reached Polymarket {lag} after the jump (build {tim.get('build', 0) * 1000:.0f}ms · "
                f"send {tim.get('post', 0) * 1000:.0f}ms)")
    if not ok and unsure:
        # the whole group request errored: make sure nothing filled anyway before calling it a miss
        time.sleep(max(0.0, t_jump + HOLD_SECS - time.time()))
        extra = 0.0
        for _ in range(3):
            try:
                extra = token_balance(tok) - held_shares(tf, o, side)
            except Exception:
                extra = 0.0
            if extra >= 1:
                break
            time.sleep(1)
        if extra >= 1:
            ok, note = True, "group request errored but shares arrived — cost estimated at the limit price"
            resp = {"makingAmount": str(round(extra * cap / 100, 4)), "takingAmount": str(round(extra, 4))}
    if not ok:
        db_exec("UPDATE lj_trades SET mode='MISSED', status='MISSED', note=?, bal_before=? WHERE id=?", (f"{note} | {lag_full}", bal0, rid))
        tg(f"⏭ {head} · missed, {short_why(note, cap)} · {lag}")
        return
    cost, shares = _amounts(resp)
    if cost <= 0 or shares <= 0:
        cost, shares = LIVE_STAKE, LIVE_STAKE / (ask / 100)
    bpx = cost / shares * 100
    t_buy = time.time()
    db_exec("UPDATE lj_trades SET status='BOUGHT', buy_cost=?, buy_shares=?, buy_px=?, buy_ts=?, bal_before=?, note=? WHERE id=?",
            (cost, shares, bpx, t_buy, bal0, (note + " | " if note else "") + lag_full, rid))
    # wait, then SELL (fill-or-kill with a floor; a few retries)
    time.sleep(max(0.0, (t_jump or t_buy) + HOLD_SECS - time.time()))
    paper_bid = best(tok, "bids")
    sold, proceeds, s_sh, note = False, 0.0, 0.0, ""
    for attempt in range(6):
        b = best(tok, "bids")
        if b is None:
            time.sleep(1)
            continue
        try:
            have = token_balance(tok)
        except Exception as e:
            have = shares
            note = f"balance check: {str(e)[:80]}"
        qty = math.floor(min(have, shares) * 100) / 100
        if qty <= 0:
            note = "no shares in the wallet yet"
            time.sleep(1)
            continue
        try:
            ok, resp, note = market_order(tok, "SELL", qty, max(1, b - LIVE_SELL_SLIP))
        except Exception as e:
            ok, note = False, f"error: {str(e)[:150]}"
        if ok:
            mk, tk = _amounts(resp)
            s_sh, proceeds = (mk, tk) if mk > 0 and tk > 0 else (qty, qty * b / 100)
            sold = True
            break
        time.sleep(1)
    try:
        bal1 = usdc_balance()
    except Exception:
        bal1 = None
    pp = None if paper_bid is None else (shares * paper_bid / 100 - cost - fee(shares, ask / 100) - fee(shares, paper_bid / 100))
    if sold:
        pnl = proceeds - cost
        spx = proceeds / s_sh * 100 if s_sh > 0 else 0
        db_exec("UPDATE lj_trades SET status='SOLD', sell_proceeds=?, sell_shares=?, sell_px=?, sell_ts=?, paper_bid=?, "
                "paper_pnl=?, pnl=?, bal_after=?, result=?, note=? WHERE id=?",
                (proceeds, s_sh, spx, time.time(), paper_bid, pp, pnl, bal1, "WIN" if pnl > 0 else "LOSS", note, rid))
        tg(f"{'✅' if pnl > 0 else '❌'} {head} · {bpx:.0f}→{spx:.0f}¢ · <b>{money(pnl)}</b>"
           f" (paper {money(pp) if pp is not None else 'n/a'}) · {lag}")
    else:
        db_exec("UPDATE lj_trades SET status='HOLDING', paper_bid=?, paper_pnl=?, bal_after=?, note=? WHERE id=?",
                (paper_bid, pp, bal1, note, rid))
        tg(f"⏳ {head} · bought {bpx:.0f}¢, couldn't sell · holding to the end")


def balance_worker():
    """keep a recent USDC balance on hand without slowing down orders"""
    while True:
        try:
            if LIVE_ENABLED and not busy:
                state["bal"] = usdc_balance()
        except Exception as e:
            log.warning(f"balance: {e}")
        time.sleep(20)


def settler():
    while True:
        try:
            now = time.time()
            for r in db_query("SELECT * FROM lj_trades WHERE status='HOLDING' AND open_ts + tf*60 < ?", (now - 90,)):
                out = outcome(r["tf"], r["open_ts"])
                if not out:
                    continue
                won = out == r["side"]
                pnl = (r["buy_shares"] if won else 0) - r["buy_cost"]
                db_exec("UPDATE lj_trades SET status='SETTLED', pnl=?, result=? WHERE id=?", (pnl, "WIN" if won else "LOSS", r["id"]))
                tg(f"{'✅' if won else '❌'} held {r['tf']}m {r['side']} settled {out} · <b>{money(pnl)}</b>")
        except Exception as e:
            log.warning(f"settler: {e}")
        time.sleep(30)


# ── reports ─────────────────────────────────────────────────────────────────
def summary(since, label):
    rows = db_query("SELECT * FROM lj_trades WHERE t0>=? ORDER BY t0", (since,))
    live = [r for r in rows if r["mode"] == "LIVE" and r["pnl"] is not None]
    paper = [r for r in rows if r["mode"] == "PAPER" and r["pnl"] is not None]
    missed = sum(1 for r in rows if r["mode"] == "MISSED")
    blocked = sum(1 for r in rows if r["mode"] == "BLOCKED")
    L = [f"<b>{label}</b>"]
    if live:
        w = sum(1 for r in live if r["pnl"] > 0)
        pp = sum(r["paper_pnl"] or 0 for r in live)
        L.append(f"💵 live: {len(live)} trades · {w} wins · <b>{money(sum(r['pnl'] for r in live))}</b> "
                 f"(paper on the same trades {money(pp)})")
        L.append(f"   avg buy slip {sum((r['buy_px'] or r['ask']) - r['ask'] for r in live) / len(live):+.1f}¢ · "
                 f"holding {sum(1 for r in rows if r['status'] == 'HOLDING')}")
    if paper:
        L.append(f"📝 paper: {len(paper)} trades · {sum(1 for r in paper if r['pnl'] > 0)} wins · "
                 f"<b>{money(sum(r['pnl'] for r in paper))}</b>")
    L.append(f"not filled {missed} · blocked {blocked} · signals {len(rows)}")
    return "\n".join(L)


def status_text():
    t_day = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    with lock:
        nm = len(markets)
    L = [f"⚡ <b>LIVE BTC JUMP SNIPER</b> · {'🟢 LIVE' if LIVE_ENABLED else '📝 PAPER (LIVE_ENABLED=false)'}"
         f"{' · ⏸ PAUSED' if paused() else ''}",
         f"rule: jump ≥{JUMP_BPS:g}bp/{JUMP_WINDOW:g}s · edge ≥{MIN_EDGE:g}¢ · ask &lt;{MAX_ASK:g}¢ · under {CHEAP_CENTS:g}¢ needs "
         f"edge ≥{CHEAP_EDGE:g}¢ · ${LIVE_STAKE:g} · sell after {HOLD_SECS:g}s",
         f"limits: ${LIVE_DAILY_LOSS:g}/day · {LIVE_MAX_TRADES_HOUR}/hour · buy ≤ min(ask+{SMART_MAX:g}¢, fair−{KEEP_EDGE:g}¢) · "
         f"sell ≥bid−{LIVE_SELL_SLIP:g}¢ · decide after {EDGE_DELAY:g}s",
         f"up {(time.time() - state['started']) / 3600:.1f}h · BTC {price['px'] or 0:,.0f} · markets {nm} · jumps {state['jumps']} · "
         f"signals {state['signals']} · σ {sigma() * 1e5:.1f}e-5/s" + (f" · last error: {state['err'][:80]}" if state["err"] else ""),
         summary(t_day, "today")]
    return "\n".join(L)


def trades_text(n=12):
    rows = db_query("SELECT * FROM lj_trades ORDER BY t0 DESC LIMIT ?", (n,))
    if not rows:
        return "no signals yet"
    L = ["<b>last signals</b>"]
    for r in rows:
        t = datetime.fromtimestamp(r["t0"], TZ).strftime("%a %H:%M:%S")
        p = r["pnl"]
        L.append(f"{t} {r['tf']}m {r['side']} ask {r['ask']:g}¢ edge {r['edge']:+.0f} · {r['mode']} {r['status']} "
                 f"{money(p) if p is not None else ''} {('(paper ' + money(r['paper_pnl']) + ')') if r['mode'] == 'LIVE' and r['paper_pnl'] is not None else ''}")
    return "\n".join(L)


def telegram_worker():
    off = 0
    while True:
        try:
            r = requests.get(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates",
                             params={"offset": off, "timeout": 30}, timeout=40).json()
            for u in r.get("result", []):
                off = u["update_id"] + 1
                msg = u.get("message") or {}
                if str(msg.get("chat", {}).get("id")) != str(TELEGRAM_CHAT_ID):
                    continue
                t = (msg.get("text") or "").strip().split()[0].lower() if msg.get("text") else ""
                if t == "/status":
                    tg(status_text())
                elif t == "/trades":
                    tg(trades_text())
                elif t == "/today":
                    tg(summary(datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp(), "today"))
                elif t == "/all":
                    tg(summary(0, "all time"))
                elif t == "/balance":
                    try:
                        tg(f"💰 USDC balance: <b>${usdc_balance():,.2f}</b>")
                    except Exception as e:
                        tg(f"⚠️ balance failed: {str(e)[:200]}")
                elif t == "/ping":
                    ms = []
                    for _ in range(5):
                        a_ = time.time()
                        try:
                            requests.get(f"{CLOB_BASE}/time", timeout=5)
                            ms.append((time.time() - a_) * 1000)
                        except Exception:
                            pass
                    tg(f"🏓 Polymarket round trip from this server: {', '.join(f'{x:.0f}' for x in ms)} ms "
                       f"(median {sorted(ms)[len(ms) // 2]:.0f} ms)" if ms else "🏓 couldn't reach Polymarket")
                elif t == "/stop":
                    kv_set("paused", "1")
                    tg("⏸ paused — no new live trades. /go to resume.")
                elif t == "/go":
                    kv_set("paused", "0")
                    tg("▶️ resumed.")
                elif t == "/export":
                    rows = db_query("SELECT * FROM lj_trades ORDER BY t0")
                    if rows:
                        buf = io.StringIO()
                        w = csv.writer(buf)
                        w.writerow(rows[0].keys())
                        w.writerows([list(x) for x in rows])
                        tg_document("live_jumper.csv.gz", gzip.compress(buf.getvalue().encode()), f"{len(rows)} signals")
                    else:
                        tg("no signals yet")
                elif t in ("/help", "/start"):
                    tg("⚡ live BTC jump sniper\n/status — settings + today\n/trades — last signals\n/today · /all — totals\n"
                       "/balance — USDC in the account\n/ping — network speed to Polymarket\n/stop — pause live trading · /go — resume\n/export — all signals (CSV)")
        except Exception as e:
            log.warning(f"telegram: {e}")
            time.sleep(5)


def main():
    init_db()
    for fn in (resolver_worker, pm_worker, bn_worker, settler, telegram_worker, balance_worker):
        threading.Thread(target=fn, daemon=True).start()
    bal = ""
    if LIVE_ENABLED:
        try:
            bal = f" · USDC ${usdc_balance():,.2f} · orders {ORDER_TYPE}"
        except Exception as e:
            bal = f" · ⚠️ couldn't connect to Polymarket: {str(e)[:150]}"
    tg(f"⚡ live BTC jump sniper started — {'🟢 LIVE' if LIVE_ENABLED else '📝 PAPER (LIVE_ENABLED=false)'} · "
       f"${LIVE_STAKE:g}/trade{bal}. Send /status.")
    while True:
        time.sleep(60)


if __name__ == "__main__":
    main()
