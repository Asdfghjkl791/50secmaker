# COMBO bot (Nov 11 2026) — one bot for every BTC + ETH rule we found, live or paper.
#
#   LIVE rules (real orders once you send /live on):
#     P5   BTC Plain D5        5m  3bp BTC jump · TWAP fair (Deribit vol) - ask >= 5c · ask 30-90c                      · limit ask + 40c
#     LS5  BTC D5-TR-LS        5m  3bp · fair - ask >= 10c · ask 10-30c · R check                                          · limit +30c
#     H1C  BTC H1-LS-C         1h  2bp · Binance-candle fair - ask >= 10c · ask 10-30c · R · FIRST such signal; trade only if
#                                   other exchanges moved >= 2bp our way in the 10s before, else skip the market       · limit +10c
#     LC5  ETH D5-LC 30-95     5m  2bp ETH · fair - ask >= 5c · ask 30-95c · R · other exchanges > 0.1bp our way 0.5s after · limit +15c
#     G10C ETH D-15LS-G10C    15m  2bp · ask 10-35c · fair - ask >= 10c · <= 10 min left · others >= 2bp our way 10s before · limit +15c
#     E15  ETH D-15E          15m  2bp · fair - ask >= 5c · ask 15-95c · R · 743-840s left                                 · limit +5c
#     EH1  ETH H1-LS           1h  2bp · Binance-candle fair - ask >= 10c · ask 10-30c · R                                · limit +5c
#   PAPER rules (logged and scored, never traded unless you turn one on):
#     TR5  BTC D5-TR 30-90 · TROL BTC D-15TROL · L15 BTC D-15L · H4 BTC H4-LS · ELS5 ETH D5-LS · EH4C ETH H4-LS-C
#   "R check" = the ask 0.25s after the jump is at most 1c above the ask at the jump. One trade per rule per market.
#
# Safety: starts with live OFF · stake capped by MAX_STAKE · daily loss stop · balance floor · max open trades · never takes the
# other side of a market it holds · skips when price or Polymarket data is stale · pauses after 3 order errors in a row.
# Tracking: every trade has a paper twin (what the paper rule would have paid), timing (jump -> order -> answer), copier log
# (wallets that buy the same side right after us), daily summary at midnight Toronto time.
#
# Telegram: /status /rules /live on|off /live CODE on|off /stake X /stop /resume /pnl [today|yday|week|all] /trades [n]
#           /copiers /edge /export /quiet on|off /help
# Env: TELEGRAM_TOKEN, TELEGRAM_CHAT_ID, DB_PATH (put it on the volume, e.g. /data/combo.db), POLY_PRIVATE_KEY, POLY_FUNDER,
#      POLY_SIG_TYPE (1), STAKE (1), MAX_STAKE (5), DAILY_LOSS (10), MIN_BALANCE (5), MAX_OPEN (15), LIVE_START (off)
import os, time, json, math, sqlite3, threading, logging, gzip, io, csv
from collections import deque
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
import requests
import websocket

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("combo")

TG_TOKEN = os.environ["TELEGRAM_TOKEN"]
TG_CHAT = str(os.environ["TELEGRAM_CHAT_ID"])
DB_PATH = os.environ.get("DB_PATH", "combo.db")
env_f = lambda k, d: float(os.environ.get(k, d))
POLY_PRIVATE_KEY = os.environ.get("POLY_PRIVATE_KEY", "").strip()
POLY_FUNDER = os.environ.get("POLY_FUNDER", "").strip()
POLY_SIG_TYPE = int(os.environ.get("POLY_SIG_TYPE", "1"))
STAKE_DEFAULT = env_f("STAKE", "1")
MAX_STAKE = env_f("MAX_STAKE", "5")
DAILY_LOSS = env_f("DAILY_LOSS", "10")
MIN_BALANCE = env_f("MIN_BALANCE", "5")
MAX_OPEN = int(env_f("MAX_OPEN", "15"))
MAX_ERRORS = 3
LIVE_START = os.environ.get("LIVE_START", "off").strip().lower() in ("1", "true", "yes", "on")
FEE_RATE = 0.07

TZ = ZoneInfo("America/Toronto")
ET = ZoneInfo("America/New_York")
GAMMA = "https://gamma-api.polymarket.com"
DATA_API = "https://data-api.polymarket.com"
CLOB_BASE = "https://clob.polymarket.com"
PM_WS = "wss://ws-subscriptions-clob.polymarket.com/ws/market"
RTDS = "wss://ws-live-data.polymarket.com"
POLYBOLT = "wss://ws-live-v2.polymarket.com/ws"
DERIBIT = "https://www.deribit.com/api/v2/public"
KLINES = "https://data-api.binance.vision/api/v3/klines"
SYM = {"BTC": "btcusdt", "ETH": "ethusdt"}
FULL = {"BTC": "bitcoin", "ETH": "ethereum"}
ASSETS = ("BTC", "ETH")
LEAD_V = ("bybit", "okx", "hl", "kraken", "bitstamp", "cb")


# ── the rules ────────────────────────────────────────────────────────────────────
class Rule:
    def __init__(self, code, name, asset, tf, trig, fair, gap, lo, hi, hi_incl=True, R=False, left_max=None, left_min=None,
                 conf=None, trol=False, lc=False, cap=10, live=False):
        self.__dict__.update(locals())
        del self.__dict__["self"]


RULES = [
    Rule("P5", "BTC Plain D5", "BTC", 5, 3, "tw_d", 5, 30, 90, cap=40, live=True),
    Rule("LS5", "BTC D5-TR-LS", "BTC", 5, 3, "tw_d", 10, 10, 30, hi_incl=False, R=True, cap=30, live=True),
    Rule("H1C", "BTC H1-LS-C", "BTC", 60, 2, "bn_d", 10, 10, 30, hi_incl=False, R=True, conf="first", cap=10, live=True),
    Rule("LC5", "ETH D5-LC 30-95", "ETH", 5, 2, "tw_d", 5, 30, 95, R=True, lc=True, cap=15, live=True),
    Rule("G10C", "ETH D-15LS-G10C", "ETH", 15, 2, "tw_d", 10, 10, 35, hi_incl=False, left_max=600, conf="filter", cap=15, live=True),
    Rule("E15", "ETH D-15E", "ETH", 15, 2, "tw_d", 5, 15, 95, R=True, left_min=743, left_max=840, cap=5, live=True),
    Rule("EH1", "ETH H1-LS", "ETH", 60, 2, "bn_d", 10, 10, 30, hi_incl=False, R=True, cap=5, live=True),
    Rule("TR5", "BTC D5-TR 30-90", "BTC", 5, 3, "tw_d", 5, 30, 90, R=True, cap=40),
    Rule("TROL", "BTC D-15TROL", "BTC", 15, 3, "tw_o", 5, 15, 95, R=True, trol=True, cap=40),
    Rule("L15", "BTC D-15L", "BTC", 15, 3, "tw_o", 8, 20, 90, left_max=600, cap=15),
    Rule("H4", "BTC H4-LS", "BTC", 240, 2, "tw_d", 10, 10, 30, hi_incl=False, R=True, cap=15),
    Rule("ELS5", "ETH D5-LS", "ETH", 5, 2, "tw_d", 10, 10, 30, hi_incl=False, R=True, left_max=150, cap=20),
    Rule("EH4C", "ETH H4-LS-C", "ETH", 240, 2, "tw_d", 10, 10, 30, hi_incl=False, R=True, conf="first", cap=10),
]
RULE = {r.code: r for r in RULES}
PLAN = {a: sorted({r.tf for r in RULES if r.asset == a}) for a in ASSETS}

# ── shared state ─────────────────────────────────────────────────────────────────
lock = threading.RLock()
px = {a: {} for a in ASSETS}                 # px[asset][venue] = deque((t, mid))
px1s = {a: deque(maxlen=4000) for a in ASSETS}
cl = {a: deque(maxlen=20000) for a in ASSETS}          # (chainlink_ts, received_ts, value)
tw_feed = {a: deque(maxlen=20000) for a in ASSETS}     # Polymarket 60s TWAP feed (ts, value)
ivs = {a: {"ts": 0, "iv": None} for a in ASSETS}   # recorder method (ETH rules, BTC 1h/4h)
iv50 = {"ts": 0, "iv": None}                          # 50secmaker method (BTC 5m/15m rules were found with this one)
markets = {}                                 # (asset, tf, o) -> {"up", "dn", "cond", "slug"}
opens = {}                                   # (asset, tf, o) -> {"bn", "cl", "tw"}
books = {}                                   # token -> {"asks": {c: sz}, "bids": {c: sz}}
book_ts = {}                                 # token -> time of its last book update (to spot stale books)
st = {"started": time.time(), "pm_msg": 0.0, "moves2": 0, "moves3": 0, "signals": 0, "err": {}, "errors_in_row": 0,
      "balance": None, "balance_ts": 0}
last2, last3 = {}, {}
done = set()                                 # (code, asset, tf, o) traded / decided
dlock = threading.Lock()
order_lock = threading.Lock()
_outcomes = {}


def _err(k, e):
    st["err"][k] = f"{datetime.now(TZ).strftime('%H:%M')} {str(e)[:140]}"
    log.warning(f"{k}: {e}")


def money(x):
    return f"{'+' if x >= 0 else '-'}${abs(x):.2f}"


def fee_of(sh, cost):
    if sh <= 0:
        return 0.0
    p = cost / sh
    return math.ceil(sh * FEE_RATE * p * (1 - p) * 100 - 1e-9) / 100


# ── storage ──────────────────────────────────────────────────────────────────────
_dbl = threading.Lock()


def db():
    c = sqlite3.connect(DB_PATH, timeout=30)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA journal_mode=WAL")
    return c


def dbx(sql, args=()):
    with _dbl:
        c = db()
        try:
            cur = c.execute(sql, args)
            c.commit()
            return cur.lastrowid
        finally:
            c.close()


def dbq(sql, args=()):
    with _dbl:
        c = db()
        try:
            return [dict(r) for r in c.execute(sql, args).fetchall()]
        finally:
            c.close()


def init_db():
    dbx("""CREATE TABLE IF NOT EXISTS trades (id INTEGER PRIMARY KEY AUTOINCREMENT, code TEXT, rule TEXT, asset TEXT, tf INTEGER, o INTEGER,
        side TEXT, mode TEXT, status TEXT, t0 REAL, feed TEXT, bps REAL, ask0 REAL, a25 REAL, fair REAL, gap REAL, left_s REAL,
        m10 REAL, m2 REAL, p05 REAL, cap REAL, stake REAL, token TEXT, cond TEXT,
        cost REAL, shares REAL, buy_px REAL, t_sent REAL, t_resp REAL, lag REAL, note TEXT,
        p_cost1 REAL, p_sh1 REAL, p_cost100 REAL, p_sh100 REAL, p_px REAL,
        outcome TEXT, won INTEGER, pnl REAL, p_pnl1 REAL, p_pnl100 REAL, settled_ts REAL, copy_checked INTEGER DEFAULT 0)""")
    dbx("CREATE INDEX IF NOT EXISTS trades_t0 ON trades (t0)")
    for col in ("bk_age REAL", "a0_ts REAL", "a25_ts REAL"):
        try:
            dbx(f"ALTER TABLE trades ADD COLUMN {col}")
        except sqlite3.OperationalError:
            pass
    dbx("""CREATE TABLE IF NOT EXISTS copiers (id INTEGER PRIMARY KEY AUTOINCREMENT, trade_id INTEGER, ts REAL, wallet TEXT, name TEXT,
        delay REAL, size REAL, price REAL)""")
    dbx("CREATE TABLE IF NOT EXISTS moves (t0 REAL, asset TEXT, trig INTEGER, feed TEXT, bps REAL, fut_lag REAL)")
    dbx("CREATE TABLE IF NOT EXISTS stats (day TEXT, code TEXT, k TEXT, n INTEGER, PRIMARY KEY (day, code, k))")
    dbx("CREATE TABLE IF NOT EXISTS kv (k TEXT PRIMARY KEY, v TEXT)")


_kvc = {}


def kv_get(k, d=None):
    hit = _kvc.get(k)
    if hit and time.time() - hit[0] < 2:
        return hit[1] if hit[1] is not None else d
    r = dbq("SELECT v FROM kv WHERE k=?", (k,))
    v = r[0]["v"] if r else None
    _kvc[k] = (time.time(), v)
    return v if v is not None else d


def kv_set(k, v):
    dbx("INSERT OR REPLACE INTO kv (k, v) VALUES (?,?)", (k, str(v)))
    _kvc.pop(k, None)


def day_str(t=None):
    return datetime.fromtimestamp(t or time.time(), TZ).strftime("%Y-%m-%d")


def bump(code, k, n=1):
    try:
        dbx("INSERT INTO stats (day, code, k, n) VALUES (?,?,?,?) ON CONFLICT(day, code, k) DO UPDATE SET n = n + ?", (day_str(), code, k, n, n))
    except Exception as e:
        _err("stats", e)


# ── settings (kept in the database so a restart keeps them) ──────────────────────
def live_on():
    return kv_get("live_on", "1" if LIVE_START else "0") == "1"


def live_codes():
    v = kv_get("live_rules")
    return set(v.split(",")) - {""} if v is not None else {r.code for r in RULES if r.live}


def stake():
    try:
        return min(MAX_STAKE, max(1.0, float(kv_get("stake", STAKE_DEFAULT))))
    except ValueError:
        return min(MAX_STAKE, STAKE_DEFAULT)


def paused():
    return kv_get("paused", "")


def quiet():
    return kv_get("quiet", "0") == "1"


# ── Telegram ─────────────────────────────────────────────────────────────────────
def tg(msg):
    try:
        requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage", data={"chat_id": TG_CHAT, "text": msg[:4000],
                      "disable_web_page_preview": "true"}, timeout=15)
    except Exception as e:
        log.warning(f"tg: {e}")


def tg_doc(name, data, caption=""):
    try:
        requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendDocument", data={"chat_id": TG_CHAT, "caption": caption[:1000]},
                      files={"document": (name, data)}, timeout=120)
    except Exception as e:
        log.warning(f"tg doc: {e}")


# ── Polymarket trading (same calls as the 50secmaker live bot) ──────────────────
_clob = None
_clob_lock = threading.Lock()


def clob():
    global _clob
    with _clob_lock:
        if _clob is not None:
            return _clob
        if not POLY_PRIVATE_KEY:
            raise RuntimeError("POLY_PRIVATE_KEY is not set")
        if POLY_SIG_TYPE in (1, 2) and not POLY_FUNDER:
            raise RuntimeError("POLY_FUNDER (your Polymarket wallet address) is not set")
        from py_clob_client_v2 import ClobClient
        c = ClobClient(CLOB_BASE, chain_id=137, key=POLY_PRIVATE_KEY, signature_type=POLY_SIG_TYPE, funder=POLY_FUNDER or None)
        c.set_api_creds(c.create_or_derive_api_key())
        _clob = c
        log.info("[LIVE] connected to Polymarket")
        return c


def usdc_balance():
    from py_clob_client_v2 import BalanceAllowanceParams, AssetType
    r = clob().get_balance_allowance(BalanceAllowanceParams(asset_type=AssetType.COLLATERAL, signature_type=POLY_SIG_TYPE))
    return float(r.get("balance", 0)) / 1e6


def _amounts(resp):
    try:
        return float(resp.get("makingAmount") or 0), float(resp.get("takingAmount") or 0)
    except Exception:
        return 0.0, 0.0


warmed = set()


def warm(token):
    """sign a throwaway order (never sent) so market/fee info is cached before a real trade needs it"""
    if token in warmed:
        return
    try:
        from py_clob_client_v2 import MarketOrderArgs, OrderType, Side
        clob().create_market_order(MarketOrderArgs(token_id=token, amount=1.0, side=Side.BUY, price=0.01, order_type=OrderType.FOK))
        warmed.add(token)
    except Exception as e:
        _err("warm", e)


def warm_worker():
    """while live is on: pre-sign for every market a live rule can trade, so the real order isn't slowed by first-time lookups"""
    while True:
        try:
            if live_on() and POLY_PRIVATE_KEY:
                lc = live_codes()
                with lock:
                    ks = list(markets.items())
                for (a, tf, o), v in ks:
                    if any(r.asset == a and r.tf == tf and r.code in lc for r in RULES):
                        for t in (v["up"], v["dn"]):
                            if t not in warmed:
                                warm(t)
                if len(warmed) > 3000:
                    warmed.clear()
        except Exception as e:
            _err("warm_worker", e)
        time.sleep(5)


def init_clob():
    try:
        clob()
    except Exception as e:
        _err("clob", e)
        tg(f"⚠️ couldn't connect to Polymarket for trading: {str(e)[:200]}")


def fast_post(c, order, ot):
    try:
        import py_clob_client_v2.client as cm
        owner = c.creds.api_key or ""
        payload = (cm.order_to_json_v2(order, owner, ot, False, False) if cm._is_v2_order(order)
                   else cm.order_to_json_v1(order, owner, ot, False, False))
        ser = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
        headers = c._l2_headers("POST", cm.POST_ORDER, body=payload, serialized_body=ser)
        return c._post(f"{c.host}{cm.POST_ORDER}", headers=headers, data=ser)
    except (AttributeError, ImportError, TypeError) as e:
        log.warning(f"[LIVE] fast_post fallback: {e}")
        return c.post_order(order, ot)


def buy(token, dollars, limit_c, tim):
    """FAK buy: fills what it can at or below the limit, cancels the rest. Returns (ok, resp, note)."""
    from py_clob_client_v2 import MarketOrderArgs, OrderType, Side
    with order_lock:
        t0 = time.time()
        lim = max(0.01, min(0.99, round(limit_c / 100.0, 2)))
        order = clob().create_market_order(MarketOrderArgs(token_id=token, amount=round(dollars, 2), side=Side.BUY, price=lim,
                                                           order_type=OrderType.FAK))
        t1 = time.time()
        try:
            resp = fast_post(clob(), order, OrderType.FAK) or {}
        except Exception as e:
            resp = {"success": False, "errorMsg": str(e)[:200]}
        t2 = time.time()
    tim.update(build=t1 - t0, sent=t1, resp=t2)
    log.info(f"[LIVE] buy build {t1 - t0:.2f}s post {t2 - t1:.2f}s resp {str(resp)[:300]}")
    if not isinstance(resp, dict):
        resp = {"success": False, "errorMsg": str(resp)[:200]}
    if not resp.get("success", False) or resp.get("errorMsg"):
        return False, resp, str(resp.get("errorMsg") or resp)[:200]
    mk, tk = _amounts(resp)
    if str(resp.get("status", "")).lower() != "matched" and tk <= 0:
        return False, resp, f"status={resp.get('status')}"
    return True, resp, ""


def is_no_fill(note):
    n = (note or "").lower()
    return any(w in n for w in ("no orders found", "no match", "fak", "fully filled or killed", "status=unmatched", "status=delayed"))


# ── windows / markets ────────────────────────────────────────────────────────────
def window(tf, now):
    if tf == 60:
        return int(datetime.fromtimestamp(now, tz=ET).replace(minute=0, second=0, microsecond=0).timestamp())
    if tf == 240:
        e = datetime.fromtimestamp(now, tz=ET)
        return int(e.replace(hour=(e.hour // 4) * 4, minute=0, second=0, microsecond=0).timestamp())
    return int(now // (tf * 60)) * tf * 60


def slug(asset, tf, o):
    if tf == 240:
        return f"{asset.lower()}-updown-4h-{o}"
    if tf == 60:
        d = datetime.fromtimestamp(o, tz=ET)
        h12 = d.strftime("%I").lstrip("0") or "12"
        return f"{FULL[asset]}-up-or-down-{d.strftime('%B').lower()}-{d.day}-{d.year}-{h12}{d.strftime('%p').lower()}-et"
    return f"{asset.lower()}-updown-{tf}m-{o}"


def _gamma_event(s):
    arr = requests.get(f"{GAMMA}/events", params={"slug": s}, timeout=10).json()
    return arr[0] if isinstance(arr, list) and arr else (arr if isinstance(arr, dict) else {})


def market_worker():
    miss = {}
    while True:
        try:
            now = time.time()
            for a, tfs in PLAN.items():
                for tf in tfs:
                    o = window(tf, now)
                    k = (a, tf, o)
                    if k in markets or now - miss.get(k, 0) < 20:
                        continue
                    ev = _gamma_event(slug(a, tf, o))
                    mk = (ev.get("markets") or [{}])[0]
                    toks = json.loads(mk.get("clobTokenIds") or "[]")
                    if len(toks) == 2:
                        with lock:
                            markets[k] = {"up": str(toks[0]), "dn": str(toks[1]), "cond": mk.get("conditionId"), "slug": slug(a, tf, o)}
                    else:
                        miss[k] = now
            with lock:
                for k in [k for k in markets if k[2] + k[1] * 60 + 120 < now]:
                    markets.pop(k, None)
            if len(miss) > 5000:
                miss.clear()
        except Exception as e:
            _err("markets", e)
        time.sleep(5)


def open_worker():
    """Binance 1m open at each window start, first Chainlink tick, TWAP-feed value at the start second"""
    while True:
        try:
            now = time.time()
            with lock:
                ks = list(markets)
            for k in ks:
                a, tf, o = k
                d = opens.setdefault(k, {})
                if "bn" not in d and now >= o + 3:
                    j = requests.get(KLINES, params={"symbol": SYM[a].upper(), "interval": "1m", "startTime": o * 1000, "limit": 1}, timeout=8).json()
                    if j and int(j[0][0]) == o * 1000:
                        d["bn"] = float(j[0][1])
                if "cl" not in d:
                    t = next((v for ts, rt, v in list(cl[a]) if o <= ts < o + 5), None)
                    if t:
                        d["cl"] = t
                if "tw" not in d and now >= o + 1:
                    v = next((v for ts, v in list(tw_feed[a]) if abs(ts - o) < 0.5), None)
                    if v:
                        d["tw"] = v
            for k in [k for k in opens if k[2] + k[1] * 60 + 3600 < now]:
                opens.pop(k, None)
        except Exception as e:
            _err("opens", e)
        time.sleep(2)


def outcome(asset, tf, o):
    k = (asset, tf, o)
    if k in _outcomes:
        return _outcomes[k]
    ev = _gamma_event(slug(asset, tf, o))
    mk = (ev.get("markets") or [{}])[0]
    try:
        op_ = [float(x) for x in json.loads(mk.get("outcomePrices") or "[]")]
    except Exception:
        op_ = []
    oc = None
    if len(op_) == 2 and max(op_) >= 0.99:
        oc = "UP" if op_[0] > op_[1] else "DOWN"
        _outcomes[k] = oc
    return oc


# ── price feeds ──────────────────────────────────────────────────────────────────
def _push(a, venue, p, now=None, every=0.05):
    if not p or p <= 0:
        return
    now = now or time.time()
    q = px[a].setdefault(venue, deque(maxlen=20000))
    if not q or now - q[-1][0] >= every:
        q.append((now, p))


def _run_ws(name, url, on_msg, subs=None, ping=None, ping_every=15, timeout=30):
    while True:
        try:
            ws = websocket.create_connection(url, timeout=10)
            ws.settimeout(timeout)
            for s in (subs or []):
                ws.send(s if isinstance(s, str) else json.dumps(s))
            log.info(f"{name} connected")
            lp = time.time()
            while True:
                if ping and time.time() - lp > ping_every:
                    ws.send(ping if isinstance(ping, str) else json.dumps(ping))
                    lp = time.time()
                raw = ws.recv()
                if not raw or raw in ("pong", "PONG") or raw[0] not in "{[":
                    continue
                on_msg(json.loads(raw))
        except Exception as e:
            _err(name, e)
        time.sleep(5)


def binance_book_worker(venue):
    url = {"vis": "wss://data-stream.binance.vision/stream?streams=",
           "spot": "wss://stream.binance.com:9443/stream?streams=",
           "fut": "wss://fstream.binance.com/stream?streams="}[venue] + "/".join(f"{SYM[a]}@bookTicker" for a in ASSETS)
    rev = {v.upper(): k for k, v in SYM.items()}

    def on(m):
        d = m.get("data") or {}
        a = rev.get(str(d.get("s", "")).upper())
        if not a:
            return
        now = time.time()
        p = (float(d["b"]) + float(d["a"])) / 2
        if venue == "fut" and d.get("E"):
            st["fut_lag"] = round(now - float(d["E"]) / 1000, 3)     # our clock minus Binance's (network delay + clock offset)
        _push(a, venue, p, now, every=0.02)
        if venue == "vis" and (not px1s[a] or now - px1s[a][-1][0] >= 1):
            px1s[a].append((now, p))
        check_trigger(a, venue, now)
    _run_ws("binance_" + venue, url, on)


def lead_worker(v):
    cs = list(ASSETS)
    if v == "bybit":
        url, subs, ping = "wss://stream.bybit.com/v5/public/linear", [{"op": "subscribe", "args": [f"orderbook.1.{a}USDT" for a in cs]}], {"op": "ping"}
    elif v == "okx":
        url, subs, ping = "wss://ws.okx.com:8443/ws/v5/public", [{"op": "subscribe", "args": [{"channel": "bbo-tbt", "instId": f"{a}-USDT-SWAP"} for a in cs]}], "ping"
    elif v == "hl":
        url, subs, ping = "wss://api.hyperliquid.xyz/ws", [{"method": "subscribe", "subscription": {"type": "bbo", "coin": a}} for a in cs], {"method": "ping"}
    elif v == "kraken":
        url, subs, ping = "wss://ws.kraken.com/v2", [{"method": "subscribe", "params": {"channel": "ticker", "symbol": [f"{a}/USD" for a in cs], "event_trigger": "bbo"}}], {"method": "ping"}
    elif v == "bitstamp":
        url, subs, ping = "wss://ws.bitstamp.net", [{"event": "bts:subscribe", "data": {"channel": f"order_book_{a.lower()}usd"}} for a in cs], None
    else:
        url, subs, ping = "wss://ws-feed.exchange.coinbase.com", [{"type": "subscribe", "product_ids": [f"{a}-USD" for a in cs], "channels": ["ticker"]}], None
    bb = {}

    def on(m):
        now = time.time()
        if v == "bybit":
            a = str(m.get("topic", "")).replace("orderbook.1.", "").replace("USDT", "")
            d = m.get("data") or {}
            if a not in px or not d:
                return
            b = bb.setdefault(a, [None, None])
            if d.get("b") and float(d["b"][0][1]) > 0:
                b[0] = float(d["b"][0][0])
            if d.get("a") and float(d["a"][0][1]) > 0:
                b[1] = float(d["a"][0][0])
            if b[0] and b[1]:
                _push(a, v, (b[0] + b[1]) / 2, now)
        elif v == "okx":
            a = str((m.get("arg") or {}).get("instId", "")).split("-")[0]
            for d in m.get("data") or []:
                if a in px and d.get("bids") and d.get("asks"):
                    _push(a, v, (float(d["bids"][0][0]) + float(d["asks"][0][0])) / 2, now)
        elif v == "hl":
            d = m.get("data") or {}
            if isinstance(d, dict) and d.get("coin") in px and d.get("bbo") and all(d["bbo"]):
                _push(d["coin"], v, (float(d["bbo"][0]["px"]) + float(d["bbo"][1]["px"])) / 2, now)
        elif v == "kraken":
            if m.get("channel") == "ticker":
                for d in m.get("data") or []:
                    a = str(d.get("symbol", "")).split("/")[0]
                    if a in px and d.get("bid") and d.get("ask"):
                        _push(a, v, (float(d["bid"]) + float(d["ask"])) / 2, now)
        elif v == "bitstamp":
            a = str(m.get("channel", "")).replace("order_book_", "").replace("usd", "").upper()
            d = m.get("data") or {}
            if a in px and d.get("bids") and d.get("asks"):
                _push(a, v, (float(d["bids"][0][0]) + float(d["asks"][0][0])) / 2, now)
        else:
            if m.get("type") == "ticker":
                a = str(m.get("product_id", "")).split("-")[0]
                if a in px and m.get("best_bid") and m.get("best_ask"):
                    _push(a, "cb", (float(m["best_bid"]) + float(m["best_ask"])) / 2, now)
    _run_ws("lead_" + v, url, on, subs, ping)


def _points(m):
    out = []

    def walk(x):
        if isinstance(x, dict):
            v, ts = x.get("value"), x.get("timestamp") or x.get("ts")
            if v is not None and ts is not None:
                try:
                    tsf = float(ts)
                    out.append((tsf / 1000 if tsf > 1e11 else tsf, float(v), str(x.get("symbol", ""))))
                    return
                except (TypeError, ValueError):
                    pass
            for k in ("payload", "data", "snapshot"):
                if k in x:
                    walk(x[k])
        elif isinstance(x, list):
            for y in x:
                walk(y)
    walk(m)
    return out


def chainlink_worker():
    """the Chainlink prices the 5m/15m/4h markets settle on (Polymarket's public live-data feed)"""
    subs = [{"action": "subscribe", "subscriptions": [{"topic": "crypto_prices_chainlink", "type": "*", "filters": json.dumps({"symbol": f"{a.lower()}/usd"})} for a in ASSETS]}]
    sym = {f"{a.lower()}/usd": a for a in ASSETS}

    def on(m):
        now = time.time()
        top = str((m.get("payload") or {}).get("symbol", "")).lower() if isinstance(m.get("payload"), dict) else ""
        for ts, v, s in _points(m):
            a = sym.get((s or top).lower())
            if not a:
                continue
            q = cl[a]
            if not q or ts > q[-1][0]:
                q.append((ts, now, v))
                _push(a, "cl", v, now, every=0)
    _run_ws("chainlink", RTDS, on, subs, "PING", ping_every=5)


def twap_feed_worker():
    """Polymarket's own 60s TWAP feed (needs API creds: from the private key, or POLY_API_KEY/SECRET/PASSPHRASE)"""
    while True:
        k, s, p = (os.environ.get(x, "") for x in ("POLY_API_KEY", "POLY_API_SECRET", "POLY_API_PASSPHRASE"))
        if not (k and s and p) and POLY_PRIVATE_KEY:
            try:
                cr = clob().creds
                k, s, p = cr.api_key, cr.api_secret, cr.api_passphrase
            except Exception as e:
                _err("twap_creds", e)
        if k and s and p:
            break
        time.sleep(300)
    subs = [{"op": "auth", "rid": "a1", "auth": {"apiKey": k, "secret": s, "passphrase": p}},
            {"op": "subscribe", "rid": "s1", "subscriptions": [{"channel": "price.crypto.twap", "filter": {"symbol": f"{a.lower()}usd", "window_seconds": 60}} for a in ASSETS]}]
    sym = {f"{a.lower()}usd": a for a in ASSETS}

    def on(m):
        if "twap" not in str(m.get("channel", "")):
            return
        top = str(((m.get("payload") or {}) if isinstance(m.get("payload"), dict) else {}).get("symbol", "")).lower()
        for ts, v, s_ in _points(m):
            a = sym.get((s_ or top).lower())
            if a and (not tw_feed[a] or ts > tw_feed[a][-1][0]):
                tw_feed[a].append((ts, v))
    _run_ws("twap_feed", POLYBOLT, on, subs, None)


def deribit_worker():
    """Deribit at-the-money implied vol (nearest expiry >= 1h) per coin, once a minute"""
    while True:
        t = time.time()
        for a in ASSETS:
            try:
                opts = (requests.get(f"{DERIBIT}/get_book_summary_by_currency", params={"currency": a, "kind": "option"}, timeout=15).json() or {}).get("result") or []
                by = {}
                for x in opts:
                    p = (x.get("instrument_name") or "").split("-")
                    if len(p) != 4 or not x.get("mark_iv"):
                        continue
                    try:
                        e = datetime.strptime(p[1], "%d%b%y").replace(hour=8, tzinfo=timezone.utc).timestamp()
                        K, F = float(p[2]), float(x.get("underlying_price") or 0)
                    except Exception:
                        continue
                    if e > t and F > 0:
                        by.setdefault(e, []).append((K, F, float(x["mark_iv"])))
                if a == "BTC":                          # nearest expiry >= 2h away, up to 4 strikes within 3% of the price
                    far = [e for e in by if e - t >= 7200]
                    if far:
                        e = min(far)
                        F = by[e][0][1]
                        allp = sorted((abs(K / F - 1), iv) for K, F_, iv in by[e])
                        pts = [x for x in allp if x[0] <= 0.03][:4] or allp[:2]
                        iv50.update(ts=t, iv=round(sum(v for _, v in pts) / len(pts), 2))
                for e in sorted(by)[:3]:
                    if (e - t) / 3600 < 1 and len(by) > 1:
                        continue
                    pts = by[e]
                    F = pts[0][1]
                    atm = [iv for K, F_, iv in pts if abs(K / F - 1) <= 0.01] or [iv for _, iv in sorted((abs(K / F - 1), iv) for K, F_, iv in pts)[:2]]
                    ivs[a] = {"ts": t, "iv": round(sum(atm) / len(atm), 2)}
                    break
            except Exception as e:
                _err("deribit_" + a, e)
        time.sleep(max(5, 60 - (time.time() - t)))


# ── Polymarket books ─────────────────────────────────────────────────────────────
def pm_handle(data):
    for m in (data if isinstance(data, list) else [data]):
        if not isinstance(m, dict):
            continue
        st["pm_msg"] = time.time()
        et = m.get("event_type")
        with lock:
            if et == "book":
                book_ts[str(m.get("asset_id"))] = st["pm_msg"]
                books[str(m.get("asset_id"))] = {"bids": {round(float(x["price"]) * 100, 3): float(x["size"]) for x in (m.get("bids") or m.get("buys") or [])},
                                                 "asks": {round(float(x["price"]) * 100, 3): float(x["size"]) for x in (m.get("asks") or m.get("sells") or [])}}
            elif et == "price_change":
                for ch in (m.get("price_changes") or m.get("changes") or []):
                    tok = str(ch.get("asset_id") or m.get("asset_id"))
                    book_ts[tok] = st["pm_msg"]
                    b = books.setdefault(tok, {"bids": {}, "asks": {}})
                    lvl = b["bids"] if str(ch.get("side", "")).upper() == "BUY" else b["asks"]
                    p, sz = round(float(ch["price"]) * 100, 3), float(ch.get("size", 0))
                    if sz <= 0:
                        lvl.pop(p, None)
                    else:
                        lvl[p] = sz


def pm_worker():
    while True:
        try:
            with lock:
                toks = tuple(sorted(t for v in markets.values() for t in (v["up"], v["dn"])))
            if not toks:
                time.sleep(2)
                continue
            ws = websocket.create_connection(PM_WS, timeout=10)
            ws.settimeout(15)
            ws.send(json.dumps({"assets_ids": list(toks), "type": "market"}))
            lp = time.time()
            cur = toks
            while True:
                if time.time() - lp > 10:
                    ws.send("PING")
                    lp = time.time()
                    with lock:
                        cur = tuple(sorted(t for v in markets.values() for t in (v["up"], v["dn"])))
                    if cur != toks:
                        break
                raw = ws.recv()
                if raw and raw[0] in "{[":
                    pm_handle(json.loads(raw))
            ws.close()
            with lock:
                for t in [t for t in books if t not in set(cur)]:
                    books.pop(t, None)
        except Exception as e:
            _err("pm", e)
            time.sleep(2)


def asks_of(tok, n=12):
    with lock:
        b = books.get(tok) or {}
        a = sorted((p, s) for p, s in (b.get("asks") or {}).items() if p < 100)[:n]
    return [[p, s] for p, s in a]


def walk(lad, dollars, cap):
    spent = sh = 0.0
    for p, sz in lad:
        if p > cap:
            break
        c = p / 100 * sz
        if spent + c >= dollars:
            sh += (dollars - spent) / (p / 100)
            spent = dollars
            break
        spent += c
        sh += sz
    return spent, sh


# ── fair prices (same formulas as the recorder the rules were found on) ─────────
def ncdf(x):
    return 0.5 * (1 + math.erf(x / math.sqrt(2)))


def sigma(a):
    pts = [p for p in list(px1s[a]) if p[0] >= time.time() - 900]
    r = [(math.log(y / x)) ** 2 / (t1 - t0) for (t0, x), (t1, y) in zip(pts, pts[1:]) if t1 > t0 and x > 0 and y > 0]
    return max(2e-5, math.sqrt(sum(r) / len(r))) if len(r) >= 30 else None


def sigma_iv(a, tf=None):
    d = iv50 if (a == "BTC" and tf in (5, 15)) else (ivs.get(a) or {})
    if not d.get("iv") or time.time() - d["ts"] > 600:
        return None
    return d["iv"] / 100 / math.sqrt(365 * 86400)


def last(a, venue, t=None):
    q = px[a].get(venue)
    if not q:
        return None
    if t is None:
        return q[-1][1]
    for tt, p in reversed(q):
        if tt <= t:
            return p
    return None


def cl_now(a, t):
    """Chainlink price brought up to time t with Binance's move since that tick arrived"""
    x = None
    for item in reversed(cl[a]):
        if item[1] <= t:
            x = item
            break
    if not x:
        return None
    ts, rt, v = x
    b0, b1 = last(a, "vis", rt), last(a, "vis", t)
    return v * b1 / b0 if b0 and b1 else v


def tw_strike(a, tf, o):
    d = opens.get((a, tf, o)) or {}
    if d.get("tw"):
        return d["tw"], "feed"
    pts = [v for ts, rt, v in list(cl[a]) if o - 62 <= ts <= o - 3]
    return (sum(pts) / len(pts), "cl") if len(pts) >= 20 else (None, None)


def fairs(a, tf, o, t):
    """chance (0-100) UP wins: bn = Binance 1m open vs Binance now; tw = the 60s-TWAP settlement rule. _o = our vol, _d = Deribit vol"""
    out = {}
    e = o + tf * 60
    left = e - t
    if left <= 0:
        return out
    op = opens.get((a, tf, o)) or {}
    vols = {"o": sigma(a), "d": sigma_iv(a, tf)}
    pb, pc = last(a, "vis", t), cl_now(a, t)
    k, _ = tw_strike(a, tf, o)
    A, B = e - 62, e - 3
    known = [v for ts, rt, v in list(cl[a]) if A <= ts <= t] if t > A else []
    for vn, s in vols.items():
        if not s:
            continue
        if op.get("bn") and pb:
            out["bn_" + vn] = round(100 * ncdf(math.log(pb / op["bn"]) / (s * math.sqrt(left))), 2)
        if k and pc:
            f = min(1.0, (t - A) / (B - A)) if (t > A and known) else 0.0
            if t >= B:
                out["tw_" + vn] = 100.0 if (sum(known) / len(known) if known else pc) >= k else 0.0
            else:
                s0 = max(t, A)
                mean = (sum(known) / len(known) if known else pc) * f + pc * (1 - f)
                sd = (1 - f) * s * math.sqrt(max(1e-9, (s0 - t) + (B - s0) / 3.0))
                out["tw_" + vn] = round(100 * ncdf(math.log(mean / k) / sd), 2)
    return out


def _move(a, venue, t0, dt, sg):
    p0, p1 = last(a, venue, t0), last(a, venue, t0 + dt)
    if not p0 or not p1:
        return None
    return ((p1 / p0 - 1) if dt > 0 else (p0 / p1 - 1)) * 1e4 * sg


def lead_mean(a, t0, dt, sg):
    """average move (bp, + = our way) of Bybit/OKX/Hyperliquid/Kraken/Bitstamp/Coinbase: dt<0 = the |dt|s before, dt>0 = after"""
    vals = [m for m in (_move(a, v, t0, dt, sg) for v in LEAD_V if v in px[a]) if m is not None]
    return sum(vals) / len(vals) if vals else None


# ── moves -> rules ───────────────────────────────────────────────────────────────
_chk = {}


def check_trigger(a, venue, now):
    q = px[a].get(venue)
    if not q or len(q) < 3:
        return
    p1 = q[-1][1]
    p0 = None
    for t, p in reversed(q):
        if t < now - 2:
            break
        p0 = p
    if not p0:
        return
    bps = (p1 / p0 - 1) * 1e4
    sg = 1 if bps > 0 else -1
    if a == "BTC" and venue in ("spot", "fut") and abs(bps) >= 3:          # BTC 5m/15m rules: 3bp jump on Binance spot/futures
        if now - last3.get(sg, 0) >= 10:
            last3[sg] = now
            st["moves3"] += 1
            threading.Thread(target=on_move, args=(a, 3, venue, round(bps, 2), now), daemon=True).start()
    if now - _chk.get((a, venue), 0) < 0.05:
        return
    _chk[(a, venue)] = now
    if venue == "fut":                                                      # ETH + 1h/4h rules were found on jumps seen by the spot feeds
        return                                                              # (the recorder's futures feed ran ~1.5s late), so futures don't count here
    if abs(bps) >= 2 and now - last2.get((a, sg), 0) >= 10:               # ETH + 1h/4h rules: 2bp jump on Binance spot / spot mirror
        last2[(a, sg)] = now
        st["moves2"] += 1
        threading.Thread(target=on_move, args=(a, 2, venue, round(bps, 2), now), daemon=True).start()


def in_range(r, ask):
    return ask >= r.lo and (ask <= r.hi if r.hi_incl else ask < r.hi)


def on_move(a, trig, feed, bps, t0):
    try:
        threading.Thread(target=dbx, args=("INSERT INTO moves (t0, asset, trig, feed, bps, fut_lag) VALUES (?,?,?,?,?,?)",
                                          (t0, a, trig, feed, bps, st.get("fut_lag"))), daemon=True).start()
        sg = 1 if bps > 0 else -1
        up = sg > 0
        rules = [r for r in RULES if r.asset == a and r.trig == trig]
        tfs = {r.tf for r in rules}
        with lock:
            mk = [(k, dict(v)) for k, v in markets.items() if k[0] == a and k[1] in tfs and k[2] <= t0 < k[2] + k[1] * 60]
        if not mk:
            return
        m10, m2 = lead_mean(a, t0, -10, sg), lead_mean(a, t0, -2, sg)
        for (a_, tf, o), m in mk:
            tok, opp = (m["up"], m["dn"]) if up else (m["dn"], m["up"])
            la = asks_of(tok, 1)
            if not la:
                continue
            a0, a0_ts = la[0][0], time.time()
            bk_age = round(a0_ts - book_ts.get(tok, 0), 3)
            fu = fairs(a, tf, o, t0)
            left = o + tf * 60 - t0
            for r in rules:
                if r.tf != tf or (r.code, a, tf, o) in done:
                    continue
                f = fu.get(r.fair)
                if f is None:
                    continue
                fv = f if up else 100 - f
                gap = fv - a0
                if not in_range(r, a0) or gap < r.gap:
                    continue
                if (r.left_max is not None and left > r.left_max) or (r.left_min is not None and left < r.left_min):
                    continue
                if r.conf == "filter" and not (m10 is not None and m10 >= 2):
                    continue
                if r.trol and not (m2 is not None and m2 <= 1.15):
                    continue
                ctx = dict(a=a, tf=tf, o=o, tok=tok, opp=opp, up=up, side="UP" if up else "DOWN", t0=t0, feed=feed, bps=bps, a0=a0,
                           fair=round(fv, 2), gap=round(gap, 2), left=round(left, 1), m10=m10, m2=m2, cond=m.get("cond"),
                           a0_ts=a0_ts, bk_age=bk_age)
                threading.Thread(target=decide, args=(r, ctx), daemon=True).start()
    except Exception as e:
        _err("on_move", e)


def decide(r, c):
    key = (r.code, c["a"], c["tf"], c["o"])
    try:
        t0 = c["t0"]
        threading.Thread(target=bump, args=(r.code, "pre"), daemon=True).start()
        a25 = None
        if r.R or r.lc:
            time.sleep(max(0.0, t0 + 0.25 - time.time()))
            la = asks_of(c["tok"], 1)
            a25, a25_ts = (la[0][0] if la else None), time.time()
            if a25 is None or a25 - c["a0"] > 1:
                bump(r.code, "r_fail")
                dbx("INSERT INTO trades (code, rule, asset, tf, o, side, mode, status, t0, feed, bps, ask0, a25, fair, gap, left_s, m10, m2, bk_age, a0_ts, a25_ts, note) "
                    "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                    (r.code, r.name, c["a"], c["tf"], c["o"], c["side"], "RFAIL", "RFAIL", t0, c["feed"], c["bps"], c["a0"], a25, c["fair"], c["gap"],
                     c["left"], c["m10"], c["m2"], c["bk_age"], c["a0_ts"], a25_ts, "R check failed (diagnostic row, never traded)"))
                return
        if r.conf == "first":                       # first signal that passes decides the market; trade it only if confirmed
            with dlock:
                if key in done:
                    return
                done.add(key)
            if not (c["m10"] is not None and c["m10"] >= 2):
                bump(r.code, "c_skip")
                dbx("INSERT INTO trades (code, rule, asset, tf, o, side, mode, status, t0, feed, bps, ask0, a25, fair, gap, left_s, m10, m2, note) "
                    "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                    (r.code, r.name, c["a"], c["tf"], c["o"], c["side"], "SKIP", "SKIP", t0, c["feed"], c["bps"], c["a0"], a25, c["fair"], c["gap"],
                     c["left"], c["m10"], c["m2"], "first signal not confirmed by other exchanges - market skipped"))
                return
        p05 = None
        if r.lc:
            time.sleep(max(0.0, t0 + 0.55 - time.time()))
            p05 = lead_mean(c["a"], t0, 0.5, 1 if c["up"] else -1)
            if p05 is None or p05 <= 0.1:
                bump(r.code, "lc_fail")
                return
        with dlock:
            if key in done and r.conf != "first":
                return
            done.add(key)
        base = a25 if a25 is not None else c["a0"]
        cap = min(99.0, base + r.cap)
        live = live_on() and r.code in live_codes()
        stk = stake()
        head = f"{r.name} {c['side']} {c['tf'] if c['tf'] < 60 else c['tf'] // 60}{'m' if c['tf'] < 60 else 'h'} · ask {c['a0']:g}¢ fair {c['fair']:.0f}¢"
        why, ok, resp, note, tim = None, False, {}, "", {}
        if live:                                   # order first, bookkeeping after (every millisecond counts)
            why = risk_check(r, c, stk)
            if not why:
                try:
                    ok, resp, note = buy(c["tok"], stk, cap, tim)
                except Exception as e:
                    ok, resp, note = False, {}, f"error: {str(e)[:150]}"
        lag = ((tim.get("resp") or time.time()) - t0) if tim else None
        rid = dbx("INSERT INTO trades (code, rule, asset, tf, o, side, mode, status, t0, feed, bps, ask0, a25, fair, gap, left_s, m10, m2, p05, cap, stake, token, cond, "
                  "t_sent, t_resp, lag, bk_age, a0_ts) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                  (r.code, r.name, c["a"], c["tf"], c["o"], c["side"], "LIVE" if live else "PAPER", "SIGNAL", t0, c["feed"], c["bps"], c["a0"], a25,
                   c["fair"], c["gap"], c["left"], c["m10"], c["m2"], p05, cap, stk if live else 1.0, c["tok"], c["cond"],
                   tim.get("sent"), tim.get("resp"), lag, c["bk_age"], c["a0_ts"]))
        st["signals"] += 1
        threading.Thread(target=paper_twin, args=(r, c, rid, cap, live, key), daemon=True).start()
        if not live:
            return
        if why:
            dbx("UPDATE trades SET status='BLOCKED', note=? WHERE id=?", (why, rid))
            bump(r.code, "blocked")
            if not why.startswith("paused") and not quiet():
                tg(f"⛔ {head} · skipped: {why}")
            if r.conf != "first":
                with dlock:
                    done.discard(key)
            return
        bump(r.code, "attempt")
        if not ok:
            nofill = is_no_fill(note)
            dbx("UPDATE trades SET status='MISSED', note=? WHERE id=?", (note[:200], rid))
            if r.conf != "first":
                with dlock:
                    done.discard(key)
            if nofill:
                st["errors_in_row"] = 0
                bump(r.code, "nofill")
                if not quiet():
                    tg(f"⏭ {head} · not filled (price ran past {cap:.0f}¢) · {lag:.2f}s")
            else:
                st["errors_in_row"] += 1
                bump(r.code, "error")
                tg(f"⚠️ {head} · order error: {note[:120]} · {lag:.2f}s")
                with dlock:
                    first_pause = st["errors_in_row"] >= MAX_ERRORS and not paused()
                    if first_pause:
                        kv_set("paused", f"paused: {MAX_ERRORS} order errors in a row")
                if first_pause:
                    tg(f"🛑 Live trading PAUSED after {MAX_ERRORS} order errors in a row. Last: {note[:150]}\nCheck, then /resume.")
            return
        st["errors_in_row"] = 0
        cost, shares = _amounts(resp)
        if cost <= 0 or shares <= 0:
            cost, shares = stk, stk / (cap / 100)
        bpx = cost / shares * 100
        bump(r.code, "filled")
        dbx("UPDATE trades SET status='HOLDING', cost=?, shares=?, buy_px=? WHERE id=?", (cost, shares, bpx, rid))
        if not quiet():
            tg(f"🎯 {head} · bought ${cost:.2f} at {bpx:.0f}¢ · {lag:.2f}s after the jump")
    except Exception as e:
        _err("decide_" + r.code, e)


def paper_twin(r, c, rid, cap, live, key):
    """what the paper rule pays: the book 1s after the jump (0.5s on 15m), up to the limit, for $1 and $100"""
    try:
        off = 0.5 if c["tf"] == 15 else 1.0
        time.sleep(max(0.0, c["t0"] + off - time.time()))
        lad = asks_of(c["tok"], 25)
        c1, s1 = walk(lad, 1.0, cap)
        c100, s100 = walk(lad, 100.0, cap)
        dbx("UPDATE trades SET p_cost1=?, p_sh1=?, p_cost100=?, p_sh100=?, p_px=? WHERE id=?",
            (c1, s1, c100, s100, (c1 / s1 * 100) if s1 > 0 else None, rid))
        if not live:
            if c1 <= 0:
                dbx("UPDATE trades SET status='MISSED', note='paper: price ran past the limit' WHERE id=?", (rid,))
                if r.conf != "first":
                    with dlock:
                        done.discard(key)
            else:
                dbx("UPDATE trades SET status='HOLDING' WHERE id=? AND status='SIGNAL'", (rid,))
    except Exception as e:
        _err("paper_twin", e)


def risk_check(r, c, stk):
    p = paused()
    if p:
        return p
    if stk > MAX_STAKE + 1e-9:
        return f"stake ${stk:g} above MAX_STAKE ${MAX_STAKE:g}"
    t_day = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    rows = dbq("SELECT pnl, cost, status, asset, tf, o, side FROM trades WHERE mode='LIVE' AND t0 >= ?", (t_day - 86400,))
    realized = sum(x["pnl"] or 0 for x in rows if x["pnl"] is not None and x["status"] == "SETTLED")
    today = dbq("SELECT COALESCE(SUM(pnl),0) s FROM trades WHERE mode='LIVE' AND status='SETTLED' AND t0 >= ?", (t_day,))[0]["s"]
    if today <= -DAILY_LOSS:
        kv_set("paused", f"paused: daily loss limit ${DAILY_LOSS:g} reached (today {money(today)})")
        tg(f"🛑 Live trading PAUSED: today's live result is {money(today)} (limit ${DAILY_LOSS:g}). It stays paused until /resume.")
        return paused()
    openp = [x for x in rows if x["status"] == "HOLDING"]
    if len(openp) >= MAX_OPEN:
        return f"{len(openp)} trades already open (max {MAX_OPEN})"
    if any(x["asset"] == c["a"] and x["tf"] == c["tf"] and x["o"] == c["o"] and x["side"] != c["side"] for x in openp):
        return "we already hold the other side of this market"
    bal = st["balance"]
    if bal is not None and time.time() - st["balance_ts"] < 300 and bal < max(MIN_BALANCE, stk):
        return f"cash ${bal:.2f} below the floor ${MIN_BALANCE:g}"
    if time.time() - st["pm_msg"] > 5:
        return "Polymarket data is stale"
    vq = px[c["a"]].get("vis")
    if not vq or time.time() - vq[-1][0] > 3:
        return "Binance price is stale"
    return None


# ── settlement, balance, copiers ─────────────────────────────────────────────────
def settler():
    while True:
        try:
            now = time.time()
            rows = dbq("SELECT * FROM trades WHERE outcome IS NULL AND mode IN ('LIVE','PAPER') AND o + tf*60 < ? AND o + tf*60 > ?", (now - 60, now - 3 * 86400))
            for x in rows:
                oc = outcome(x["asset"], x["tf"], x["o"])
                if not oc:
                    continue
                won = 1 if oc == x["side"] else 0
                pnl = None
                if x["status"] == "HOLDING" and x["mode"] == "LIVE" and (x["cost"] or 0) > 0:
                    pnl = (x["shares"] if won else 0) - x["cost"] - fee_of(x["shares"], x["cost"])
                p1 = ((x["p_sh1"] if won else 0) - x["p_cost1"] - fee_of(x["p_sh1"], x["p_cost1"])) if (x["p_cost1"] or 0) > 0 else None
                p100 = ((x["p_sh100"] if won else 0) - x["p_cost100"] - fee_of(x["p_sh100"], x["p_cost100"])) if (x["p_cost100"] or 0) > 0 else None
                status = "SETTLED" if x["status"] == "HOLDING" else x["status"]
                if x["mode"] == "PAPER" and x["status"] == "HOLDING":
                    pnl = p1
                dbx("UPDATE trades SET outcome=?, won=?, pnl=?, p_pnl1=?, p_pnl100=?, status=?, settled_ts=? WHERE id=?",
                    (oc, won, pnl, p1, p100, status, now, x["id"]))
                if x["mode"] == "LIVE" and pnl is not None and not quiet():
                    t_day = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
                    td = dbq("SELECT COALESCE(SUM(pnl),0) s, COUNT(*) n FROM trades WHERE mode='LIVE' AND status='SETTLED' AND t0 >= ?", (t_day,))[0]
                    tg(f"{'✅' if won else '❌'} {x['rule']} {x['side']} at {x['buy_px']:.0f}¢ · {money(pnl)} · today {money(td['s'])} ({td['n']} trades)")
                time.sleep(0.2)
            with dlock:
                for k in [k for k in list(done) if k[3] + k[2] * 60 < now - 600]:
                    done.discard(k)
        except Exception as e:
            _err("settler", e)
        time.sleep(20)


ALERT_UP = (50, 100, 200, 300, 500, 1000, 2000, 5000, 10000)      # cash levels worth a message (10x the next stake step)


def balance_alerts(bal):
    try:
        hi = float(kv_get("alert_hi", "0"))
        lvl = max([x for x in ALERT_UP if bal >= x] or [0])
        if lvl > hi:
            kv_set("alert_hi", lvl)
            if hi > 0 or lvl > 0:
                tg(f"💰 cash reached ${bal:.2f} (passed ${lvl:g}). Your 10x rule: stakes up to ${lvl / 10:g} are OK now (/stake, MAX_STAKE).")
        start = float(kv_get("bal_start", "0") or 0)
        warned = kv_get("alert_lo_day") == day_str()
        if start >= 5 and bal < start * 0.75 and not warned:
            kv_set("alert_lo_day", day_str())
            tg(f"📉 cash ${bal:.2f}, down {100 * (1 - bal / start):.0f}% from today's start (${start:.2f}).")
    except Exception as e:
        _err("alerts", e)


def balance_worker():
    while True:
        if POLY_PRIVATE_KEY:
            try:
                st["balance"], st["balance_ts"] = usdc_balance(), time.time()
                balance_alerts(st["balance"])
                d = day_str()
                if kv_get("bal_day") != d:
                    kv_set("bal_day", d)
                    kv_set("bal_start", f"{st['balance']:.2f}")
            except Exception as e:
                _err("balance", e)
        time.sleep(60)


def copier_worker():
    """75s after each live fill: who else bought the same side of that market around our trade (data-api, public)"""
    me = POLY_FUNDER.lower()
    while True:
        try:
            rows = dbq("SELECT id, cond, token, t_resp FROM trades WHERE mode='LIVE' AND cost > 0 AND copy_checked=0 AND t_resp < ? AND t_resp > ?",
                       (time.time() - 75, time.time() - 6 * 3600))
            for x in rows[:20]:
                if not x["cond"]:
                    dbx("UPDATE trades SET copy_checked=1 WHERE id=?", (x["id"],))
                    continue
                arr = requests.get(f"{DATA_API}/trades", params={"market": x["cond"], "limit": 500}, timeout=15).json()
                for t in (arr if isinstance(arr, list) else []):
                    try:
                        if str(t.get("asset")) != x["token"] or str(t.get("side", "")).upper() != "BUY":
                            continue
                        w = str(t.get("proxyWallet") or "").lower()
                        if not w or w == me:
                            continue
                        d = float(t.get("timestamp")) - x["t_resp"]
                        if -10 <= d <= 60:
                            dbx("INSERT INTO copiers (trade_id, ts, wallet, name, delay, size, price) VALUES (?,?,?,?,?,?,?)",
                                (x["id"], float(t.get("timestamp")), w, str(t.get("pseudonym") or t.get("name") or "")[:40], round(d, 1),
                                 float(t.get("size") or 0), float(t.get("price") or 0)))
                    except (TypeError, ValueError):
                        continue
                dbx("UPDATE trades SET copy_checked=1 WHERE id=?", (x["id"],))
                time.sleep(1)
        except Exception as e:
            _err("copiers", e)
        time.sleep(30)


# ── reports ──────────────────────────────────────────────────────────────────────
def _range(which):
    now = datetime.now(TZ)
    d0 = now.replace(hour=0, minute=0, second=0, microsecond=0)
    if which == "yday":
        return (d0 - timedelta(days=1)).timestamp(), d0.timestamp(), "yesterday"
    if which == "week":
        return (d0 - timedelta(days=6)).timestamp(), time.time() + 1, "last 7 days"
    if which == "all":
        return 0, time.time() + 1, "all time"
    return d0.timestamp(), time.time() + 1, "today"


def pnl_text(t_from, t_to, label):
    rows = dbq("SELECT * FROM trades WHERE t0 >= ? AND t0 < ? AND mode IN ('LIVE','PAPER') ORDER BY t0", (t_from, t_to))
    lines = [f"📊 {label} — live = real money, twin = what the paper rule made ($1 / $100 a trade)"]
    tl = {"n": 0, "w": 0, "pnl": 0.0, "open": 0}
    tp = {"n": 0, "w": 0, "p1": 0.0, "p100": 0.0}
    for r in RULES:
        rr = [x for x in rows if x["code"] == r.code]
        lv = [x for x in rr if x["mode"] == "LIVE" and (x["cost"] or 0) > 0]
        ls = [x for x in lv if x["pnl"] is not None]
        seen, tw = set(), []
        for x in rr:
            k = (x["asset"], x["tf"], x["o"])
            if (x["p_cost1"] or 0) > 0 and k not in seen:
                seen.add(k)
                tw.append(x)
        tws = [x for x in tw if x["p_pnl1"] is not None]
        if not rr:
            continue
        tag = "LIVE " if r.code in live_codes() else "paper"
        s = f"{tag} {r.code:<4} {r.name}: "
        if lv:
            pl = sum(x["pnl"] for x in ls)
            s += f"live {len(ls)}/{sum(x['won'] for x in ls)} won {money(pl)}" + (f" ({len(lv) - len(ls)} open)" if len(lv) > len(ls) else "") + " · "
            tl["n"] += len(ls); tl["w"] += sum(x["won"] for x in ls); tl["pnl"] += pl; tl["open"] += len(lv) - len(ls)
        p1 = sum(x["p_pnl1"] for x in tws)
        p100 = sum(x["p_pnl100"] or 0 for x in tws)
        s += f"twin {len(tws)}/{sum(x['won'] for x in tws)} won {money(p1)} / {money(p100)}"
        lines.append(s)
        if r.code in live_codes():
            tp["n"] += len(tws); tp["w"] += sum(x["won"] for x in tws); tp["p1"] += p1; tp["p100"] += p100
    lines.append(f"\nLIVE total: {tl['n']} settled, {tl['w']} won, {money(tl['pnl'])}" + (f" · {tl['open']} open" if tl["open"] else ""))
    lines.append(f"Twin total (live rules): {tp['n']} trades, {tp['w']} won, {money(tp['p1'])} at $1 / {money(tp['p100'])} at $100")
    return "\n".join(lines)


def edge_text(t_from, t_to, label):
    rows = dbq("SELECT * FROM trades WHERE t0 >= ? AND t0 < ? AND mode='LIVE'", (t_from, t_to))
    d_from, d_to = day_str(t_from + 1), day_str(t_to - 1)
    stt = dbq("SELECT code, k, SUM(n) n FROM stats WHERE day >= ? AND day <= ? GROUP BY code, k", (d_from, d_to))
    S = {}
    for x in stt:
        S.setdefault(x["code"], {})[x["k"]] = x["n"]
    lines = [f"⏱ edge tracker, {label} (live orders)"]
    for r in RULES:
        rr = [x for x in rows if x["code"] == r.code]
        s = S.get(r.code, {})
        if not rr and not s:
            continue
        att = [x for x in rr if x["status"] in ("HOLDING", "SETTLED", "MISSED")]
        fil = [x for x in rr if (x["cost"] or 0) > 0]
        lags = sorted(x["lag"] for x in rr if x["lag"])
        slip = [x["buy_px"] - x["p_px"] for x in fil if x["buy_px"] and x["p_px"]]
        part = [x["cost"] / x["stake"] for x in fil if x["stake"]]
        pre, rf = s.get("pre", 0), s.get("r_fail", 0)
        lines.append(f"{r.code}: filled {len(fil)}/{len(att)}" + (f" · median {lags[len(lags) // 2]:.2f}s jump→answer" if lags else "")
                     + (f" · paid {sum(slip) / len(slip):+.1f}¢ vs paper" if slip else "") + (f" · {100 * sum(part) / len(part):.0f}% of stake filled" if part else "")
                     + (f" · R-check fails {rf}/{pre}" if pre and (r.R or r.lc) else (f" · {pre} signals" if pre else "")))
    return "\n".join(lines)


def copiers_text(days=7):
    t = time.time() - days * 86400
    n = dbq("SELECT COUNT(*) n FROM trades WHERE mode='LIVE' AND cost > 0 AND copy_checked=1 AND t_resp > ?", (t,))[0]["n"]
    rows = dbq("SELECT c.wallet, MAX(c.name) name, COUNT(DISTINCT c.trade_id) k, AVG(c.delay) d, SUM(CASE WHEN c.delay >= 2 THEN 1 ELSE 0 END) after_, "
               "SUM(CASE WHEN c.delay < 2 THEN 1 ELSE 0 END) same_ FROM copiers c WHERE c.ts > ? GROUP BY c.wallet ORDER BY k DESC LIMIT 10", (t,))
    if not n:
        return "👀 no live trades checked yet (the check runs 75s after each live fill)"
    lines = [f"👀 wallets buying the same side as us, last {days} days ({n} of our live trades checked)",
             "same time = within 2s of us (another fast bot on the same jump) · after = 2-60s later (could be copying us)"]
    for x in rows:
        if x["k"] < 2:
            continue
        lines.append(f"{x['wallet'][:6]}…{x['wallet'][-4:]} {x['name'] or ''}: {x['k']} of our {n} trades ({100 * x['k'] / n:.0f}%) · "
                     f"same time {x['same_']} · after {x['after_']} · avg {x['d']:+.0f}s")
    if len(lines) == 2:
        lines.append("nobody showed up on 2 or more of our trades yet")
    return "\n".join(lines)


def status_text():
    lc = live_codes()
    on = live_on()
    now = time.time()
    t_day = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    td = dbq("SELECT COALESCE(SUM(pnl),0) s, COUNT(*) n FROM trades WHERE mode='LIVE' AND status='SETTLED' AND t0 >= ?", (t_day,))[0]
    op = dbq("SELECT COUNT(*) n, COALESCE(SUM(cost),0) c FROM trades WHERE mode='LIVE' AND status='HOLDING'")[0]
    age = lambda a, v: f"{now - px[a][v][-1][0]:.0f}s" if px[a].get(v) else "none"
    lines = [f"🤖 COMBO bot · live trading {'ON' if on else 'OFF'}" + (f" · {paused()}" if paused() else ""),
             f"stake ${stake():g} (max ${MAX_STAKE:g}) · daily loss stop ${DAILY_LOSS:g} · cash floor ${MIN_BALANCE:g} · max open {MAX_OPEN}",
             f"live rules: {', '.join(sorted(lc)) or 'none'}",
             f"cash: {'$%.2f' % st['balance'] if st['balance'] is not None else 'unknown (no key)'} · open live trades {op['n']} (${op['c']:.2f}) · today live {money(td['s'])} ({td['n']} settled)",
             f"jumps seen: {st['moves3']} BTC 3bp · {st['moves2']} 2bp · signals {st['signals']} · markets {len(markets)} · PM data {now - st['pm_msg']:.0f}s old"
             + (f" · clock vs Binance {st['fut_lag']:+.3f}s" if st.get("fut_lag") is not None else "")]
    for a in ASSETS:
        lines.append(f"{a}: binance {age(a, 'vis')}/{age(a, 'spot')}/{age(a, 'fut')} · others " + " ".join(f"{v} {age(a, v)}" for v in LEAD_V)
                     + f" · chainlink {age(a, 'cl')} · twap feed {'%.0fs' % (now - tw_feed[a][-1][0]) if tw_feed[a] else 'none'} · deribit iv {ivs[a].get('iv')}"
                     + (f" (5m/15m: {iv50.get('iv')})" if a == "BTC" else ""))
    if st["err"]:
        lines.append("last errors: " + " | ".join(f"{k}: {v}" for k, v in list(st["err"].items())[-5:]))
    return "\n".join(lines)


def rules_text():
    lc = live_codes()
    return "📋 rules (code · name · LIVE/paper)\n" + "\n".join(f"{r.code:<4} {r.name} · {'LIVE' if r.code in lc else 'paper'} · limit +{r.cap:g}¢" for r in RULES) + \
        "\n\n/live CODE on|off to switch one rule"


def trades_text(n=12):
    rows = dbq("SELECT * FROM trades WHERE mode='LIVE' ORDER BY id DESC LIMIT ?", (n,))
    if not rows:
        return "no live trades yet"
    out = []
    for x in rows:
        t = datetime.fromtimestamp(x["t0"], TZ).strftime("%m-%d %H:%M:%S")
        res = money(x["pnl"]) if x["pnl"] is not None else x["status"].lower()
        out.append(f"{t} {x['code']} {x['side']} ask {x['ask0']:g}¢" + (f" paid {x['buy_px']:.0f}¢" if x["buy_px"] else "") +
                   (f" {x['lag']:.2f}s" if x["lag"] else "") + f" · {res}" + (f" · {x['note'][:60]}" if x["note"] and x["status"] in ("BLOCKED", "MISSED") else ""))
    return "\n".join(out)


def export():
    rows = dbq("SELECT * FROM trades ORDER BY id")
    mv = dbq("SELECT * FROM moves WHERE t0 > ? ORDER BY t0", (time.time() - 3 * 86400,))
    for name, rs in (("combo_trades.csv.gz", rows), ("combo_copiers.csv.gz", dbq("SELECT * FROM copiers ORDER BY id")), ("combo_moves.csv.gz", mv)):
        if not rs:
            continue
        buf = io.StringIO()
        w = csv.DictWriter(buf, fieldnames=list(rs[0].keys()))
        w.writeheader()
        w.writerows(rs)
        tg_doc(name, gzip.compress(buf.getvalue().encode()), f"{len(rs)} rows")


HELP = """COMBO bot commands
/status — live on/off, cash, open trades, feeds
/rules — every rule, live or paper
/live on | /live off — all live rules on/off (/stop = off)
/live CODE on|off — one rule (e.g. /live ELS5 on)
/stake 1 — dollars per live trade (max MAX_STAKE)
/resume — clear a pause (loss limit / errors)
/pnl [today|yday|week|all] — live + paper twin per rule
/trades [n] — last live trades
/edge [today|yday|week] — fill rate, speed, price vs paper
/copiers — wallets buying right after us
/export — CSV of every trade + copier log
/quiet on|off — stop/start the per-trade messages
(cash alerts come by themselves: at $50, $100, $200, $500, $1000… and if cash drops 25% in a day)"""


def handle(text):
    p = text.strip().split()
    if not p:
        return
    cmd, args = p[0].split("@")[0].lower(), p[1:]
    if cmd in ("/help", "/start"):
        tg(HELP)
    elif cmd == "/status":
        tg(status_text())
    elif cmd == "/rules":
        tg(rules_text())
    elif cmd == "/stop":
        kv_set("live_on", "0")
        tg("🛑 live trading OFF. Paper rules keep running. /live on to restart.")
    elif cmd == "/live":
        if not args:
            tg(f"live trading is {'ON' if live_on() else 'OFF'} · rules: {', '.join(sorted(live_codes()))}")
        elif args[0].lower() in ("on", "off") and len(args) == 1:
            if args[0].lower() == "on" and not POLY_PRIVATE_KEY:
                tg("can't go live: POLY_PRIVATE_KEY is not set")
                return
            kv_set("live_on", "1" if args[0].lower() == "on" else "0")
            if args[0].lower() == "on":
                try:
                    clob()
                except Exception as e:
                    kv_set("live_on", "0")
                    tg(f"can't connect to Polymarket: {e}")
                    return
            tg(f"live trading {'ON' if live_on() else 'OFF'} · ${stake():g} a trade · rules: {', '.join(sorted(live_codes()))}")
        elif len(args) == 2 and args[0].upper() in RULE and args[1].lower() in ("on", "off"):
            lc = live_codes()
            (lc.add if args[1].lower() == "on" else lc.discard)(args[0].upper())
            kv_set("live_rules", ",".join(sorted(lc)))
            extra = " (this rule hasn't finished its paper test)" if args[1].lower() == "on" and not RULE[args[0].upper()].live else ""
            tg(f"{RULE[args[0].upper()].name}: {'LIVE' if args[1].lower() == 'on' else 'paper'}{extra}")
        else:
            tg("use /live on, /live off, or /live CODE on|off (see /rules)")
    elif cmd == "/stake":
        try:
            v = float(args[0])
            if v < 1:
                tg("Polymarket's minimum is $1")
            elif v > MAX_STAKE:
                tg(f"max is ${MAX_STAKE:g} (MAX_STAKE in Railway)")
            else:
                kv_set("stake", f"{v:g}")
                tg(f"stake now ${v:g} a trade")
        except (IndexError, ValueError):
            tg(f"stake is ${stake():g} · /stake 5 to change")
    elif cmd == "/resume":
        kv_set("paused", "")
        st["errors_in_row"] = 0
        tg(f"resumed · live trading is {'ON' if live_on() else 'OFF'}")
    elif cmd == "/pnl":
        tg(pnl_text(*_range(args[0].lower() if args else "today")))
    elif cmd == "/edge":
        tg(edge_text(*_range(args[0].lower() if args else "today")))
    elif cmd == "/trades":
        tg(trades_text(int(args[0]) if args and args[0].isdigit() else 12))
    elif cmd == "/quiet":
        on_ = not args or args[0].lower() == "on"
        kv_set("quiet", "1" if on_ else "0")
        tg("quiet: no per-trade messages (pauses, errors and the midnight summary still come)" if on_ else "per-trade messages ON")
    elif cmd == "/copiers":
        tg(copiers_text())
    elif cmd == "/export":
        export()


def telegram_worker():
    off = None
    while True:
        try:
            r = requests.get(f"https://api.telegram.org/bot{TG_TOKEN}/getUpdates", params={"timeout": 25, "offset": off}, timeout=35).json()
            for u in r.get("result", []):
                off = u["update_id"] + 1
                m = u.get("message") or u.get("edited_message") or {}
                if str((m.get("chat") or {}).get("id")) != TG_CHAT or not m.get("text"):
                    continue
                try:
                    handle(m["text"])
                except Exception as e:
                    tg(f"command error: {str(e)[:200]}")
        except Exception as e:
            _err("telegram", e)
            time.sleep(5)


def daily_worker():
    """just after midnight Toronto: yesterday's summary + edge tracker + copiers"""
    while True:
        try:
            d = day_str()
            if kv_get("summary_day") is None:
                kv_set("summary_day", d)
            if kv_get("summary_day") != d and datetime.now(TZ).minute >= 1:
                kv_set("summary_day", d)
                tg(pnl_text(*_range("yday")))
                tg(edge_text(*_range("yday")))
                if dbq("SELECT 1 FROM trades WHERE mode='LIVE' AND cost > 0 LIMIT 1"):
                    tg(copiers_text(1))
        except Exception as e:
            _err("daily", e)
        time.sleep(30)


def main():
    init_db()
    for x in dbq("SELECT code, asset, tf, o FROM trades WHERE t0 > ? AND (mode='SKIP' OR cost > 0 OR p_cost1 > 0 OR status IN ('SIGNAL','HOLDING'))",
                 (time.time() - 5 * 3600,)):
        done.add((x["code"], x["asset"], x["tf"], x["o"]))      # after a restart, never trade the same market twice
    if LIVE_START and kv_get("live_on") is None:
        kv_set("live_on", "1")
    workers = [market_worker, open_worker, pm_worker, chainlink_worker, twap_feed_worker, deribit_worker, settler, balance_worker,
               copier_worker, telegram_worker, daily_worker, warm_worker]
    for fn in workers:
        threading.Thread(target=fn, daemon=True, name=fn.__name__).start()
    for v in ("vis", "spot", "fut"):
        threading.Thread(target=binance_book_worker, args=(v,), daemon=True).start()
    for v in ("bybit", "okx", "hl", "kraken", "bitstamp", "coinbase"):
        threading.Thread(target=lead_worker, args=(v,), daemon=True).start()
    if POLY_PRIVATE_KEY:
        threading.Thread(target=init_clob, daemon=True).start()
    tg(f"🤖 COMBO bot started · live trading {'ON' if live_on() else 'OFF'} · ${stake():g} a trade · "
       f"{len(live_codes())} live rules, {len(RULES) - len(live_codes())} paper · /help")
    while True:
        time.sleep(60)


if __name__ == "__main__":
    main()
