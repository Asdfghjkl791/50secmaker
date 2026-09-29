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

import os, time, json, sqlite3, logging, threading, requests, csv, io, gzip
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

# ── INVERSE: on every favorite-dip trigger, also paper-buy the OTHER side ──
# Filled at the other side's REAL best ask at that moment (never 100-minus-
# favorite), so wide 1h/4h books cost what they really cost. Tracked in its
# own table (inv_trades) with both hold-to-settle and ladder P&L.
INV_ENABLED         = os.environ.get("INV_ENABLED", "true").lower() == "true"
INV_RUNG_STEP_CENTS = float(os.environ.get("INV_RUNG_STEP_CENTS", "8"))
INV_LADDER_SELL_FRAC = float(os.environ.get("INV_LADDER_SELL_FRAC", "0.5"))
INV_SEND_EACH       = os.environ.get("INV_SEND_EACH", "false").lower() == "true"
TABLES = ("trades", "inv_trades")

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
    # New columns for inverse analysis (only filled for trades from now on).
    for col in ("opp_ask REAL", "opp_bid REAL", "entry_bid REAL",
                "peak_bid_after REAL", "min_bid_after REAL"):
        try:
            conn.execute(f"ALTER TABLE trades ADD COLUMN {col}")
        except sqlite3.OperationalError:
            pass   # already exists
    conn.execute("""CREATE TABLE IF NOT EXISTS inv_trades (
        id INTEGER PRIMARY KEY AUTOINCREMENT, created TEXT, fav_id INTEGER,
        asset TEXT, tf INTEGER, direction TEXT, open_ts INTEGER, close_ts INTEGER,
        entry_ask REAL, entry_bid REAL, fav_ask REAL, fav_bid REAL,
        peak_at_entry REAL, result TEXT, pnl REAL, ladder_sold REAL DEFAULT 0,
        ladder_proceeds REAL DEFAULT 0, hold_pnl REAL, peak_bid_after REAL,
        min_bid_after REAL)""")
    for tbl in TABLES:
        conn.execute(f"UPDATE {tbl} SET result='VOID' WHERE result='PENDING'")
    conn.commit()
    conn.close()


def db_insert_inv(fav_id, asset, tf, direction, open_ts, close_ts, entry_ask,
                  entry_bid, fav_ask, fav_bid, peak_at_entry):
    """direction = the side BOUGHT (opposite of the favorite)."""
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("""INSERT INTO inv_trades (created,fav_id,asset,tf,direction,open_ts,
                 close_ts,entry_ask,entry_bid,fav_ask,fav_bid,peak_at_entry,result)
                 VALUES (?,?,?,?,?,?,?,?,?,?,?,?,'PENDING')""",
              (datetime.now(timezone.utc).isoformat(), fav_id, asset, tf,
               direction, open_ts, close_ts, entry_ask, entry_bid, fav_ask,
               fav_bid, peak_at_entry))
    rid = c.lastrowid
    conn.commit()
    conn.close()
    return rid


def db_insert(asset, tf, direction, open_ts, close_ts, entry_ask, peak_at_entry,
              opp_ask=None, opp_bid=None, entry_bid=None):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("""INSERT INTO trades (created,asset,tf,direction,open_ts,close_ts,
                 entry_ask,peak_at_entry,result,opp_ask,opp_bid,entry_bid)
                 VALUES (?,?,?,?,?,?,?,?, 'PENDING',?,?,?)""",
              (datetime.now(timezone.utc).isoformat(), asset, tf, direction,
               open_ts, close_ts, entry_ask, peak_at_entry,
               opp_ask, opp_bid, entry_bid))
    rid = c.lastrowid
    conn.commit()
    conn.close()
    return rid


def db_resolve(rid, result, pnl, ladder_sold, ladder_proceeds, hold_pnl,
               peak_bid_after=None, min_bid_after=None, table="trades"):
    assert table in TABLES
    conn = sqlite3.connect(DB_PATH)
    conn.execute(f"""UPDATE {table} SET result=?, pnl=?, ladder_sold=?,
                    ladder_proceeds=?, hold_pnl=?, peak_bid_after=?,
                    min_bid_after=? WHERE id=?""",
                 (result, pnl, ladder_sold, ladder_proceeds, hold_pnl,
                  peak_bid_after, min_bid_after, rid))
    conn.commit()
    conn.close()


def db_scoreboard(table="trades"):
    assert table in TABLES
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute(f"""SELECT result, pnl, tf, hold_pnl, entry_ask FROM {table}
                  WHERE result IN ('WIN','LOSS')""")
    rows = c.fetchall()
    conn.close()
    wins = sum(1 for r in rows if r[0] == "WIN")
    pnl = sum(r[1] or 0 for r in rows)
    hold = sum(r[3] or 0 for r in rows)
    wr = (wins / len(rows) * 100) if rows else None
    by_tf = {}
    for r in rows:
        d = by_tf.setdefault(r[2], {"n": 0, "w": 0, "pnl": 0.0, "hold": 0.0,
                                    "px": 0.0})
        d["n"] += 1
        d["w"] += 1 if r[0] == "WIN" else 0
        d["pnl"] += r[1] or 0
        d["hold"] += r[3] or 0
        d["px"] += r[4] or 0
    return {"n": len(rows), "wins": wins, "wr": wr, "pnl": pnl, "hold": hold,
            "by_tf": by_tf}


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


# ── DATA EXPORT (for offline analysis / inverse-strategy engineering) ───────

def tg_document(filename, text, caption=""):
    """Send a text file (CSV) to the Telegram chat as a downloadable document."""
    try:
        r = requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendDocument",
            data={"chat_id": TELEGRAM_CHAT_ID, "caption": caption[:1000]},
            files={"document": (filename, text.encode("utf-8"), "text/csv")},
            timeout=120)
        ok = False
        try:
            ok = r.json().get("ok", False)
        except Exception:
            pass
        if r.status_code != 200 or not ok:
            log.error(f"[TG-DOC] REJECTED {r.status_code}: {r.text[:150]}")
            tg(f"⚠️ upload of {filename} failed ({r.status_code})")
    except Exception as e:
        log.error(f"[TG-DOC] {e}")
        tg(f"⚠️ upload of {filename} failed: {e}")


def _iso_to_ts(s):
    try:
        return datetime.fromisoformat(s).timestamp()
    except Exception:
        return None


def build_trades_csv(table="trades", tf=None):
    """Every row of a table (optionally one timeframe) + derived timing columns."""
    assert table in TABLES
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    if tf:
        rows = conn.execute(f"SELECT * FROM {table} WHERE tf=? ORDER BY id",
                            (tf,)).fetchall()
    else:
        rows = conn.execute(f"SELECT * FROM {table} ORDER BY id").fetchall()
    conn.close()
    if not rows:
        return None, 0
    cols = list(rows[0].keys())
    extra = ["entry_ts", "window_secs", "secs_into_window", "secs_left_at_entry",
             "dip_cents", "shares_total"]
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(cols + extra)
    for r in rows:
        ets = _iso_to_ts(r["created"])
        win = (r["close_ts"] - r["open_ts"]) if r["close_ts"] and r["open_ts"] else None
        into = round(ets - r["open_ts"], 1) if ets and r["open_ts"] else None
        left = round(r["close_ts"] - ets, 1) if ets and r["close_ts"] else None
        fav_px = r["fav_ask"] if "fav_ask" in cols else r["entry_ask"]
        dip = (round(r["peak_at_entry"] - fav_px, 2)
               if r["peak_at_entry"] is not None and fav_px else None)
        sh = (round(PAPER_STAKE / (r["entry_ask"] / 100.0), 4)
              if r["entry_ask"] else None)
        w.writerow([r[c] for c in cols] +
                   [round(ets, 1) if ets else None, win, into, left, dip, sh])
    return buf.getvalue(), len(rows)


def fetch_price_history(token_id, start_ts, end_ts):
    """Polymarket's per-token price history (1-minute points). Returns
    [(t, price_cents), ...] — may be empty for older/closed markets."""
    for params in ({"market": token_id, "startTs": int(start_ts),
                    "endTs": int(end_ts), "fidelity": 1},
                   {"market": token_id, "interval": "max", "fidelity": 1}):
        try:
            r = requests.get(f"{CLOB_BASE}/prices-history", params=params,
                             timeout=15)
            hist = r.json().get("history", []) if r.status_code == 200 else []
            pts = [(int(h["t"]), float(h["p"]) * 100.0) for h in hist
                   if "t" in h and "p" in h
                   and start_ts - 60 <= int(h["t"]) <= end_ts + 60]
            if pts:
                return pts
        except Exception as e:
            log.debug(f"[HIST] {token_id[:10]}: {e}")
    return []


_export_lock = threading.Lock()
_paths_io_lock = threading.Lock()
_paths_pause = threading.Event()   # set by /pausepaths, checked between markets
EXPORT_DIR = os.path.dirname(os.path.abspath(DB_PATH))
PATHS_CSV = os.path.join(EXPORT_DIR, "favdip_paths.csv")
PATHS_DONE = os.path.join(EXPORT_DIR, "favdip_paths_done.txt")
PATHS_HEADER = ["asset", "tf", "open_ts", "token_dir", "t",
                "secs_into_window", "price_cents"]
TG_PART_BYTES = 40 * 1024 * 1024   # Telegram bot upload limit is 50MB


def _market_key(asset, tf, open_ts):
    return f"{asset}|{tf}|{open_ts}"


def export_paths_worker(tf=None):
    """Price path of BOTH sides for every market the bot traded, one row per
    minute. Stored per MARKET (not per trade) so markets traded on both sides
    aren't fetched twice; join to trades on asset+tf+open_ts.
    Written to the volume as it goes and RESUMABLE: re-running /exportpaths
    after a restart skips markets already done."""
    if not _export_lock.acquire(blocking=False):
        tg("⏳ path export already running — /sendpaths sends what's done so far")
        return
    try:
        conn = sqlite3.connect(DB_PATH)
        q = "SELECT DISTINCT asset, tf, open_ts, close_ts FROM trades"
        mkts = (conn.execute(q + " WHERE tf=? ORDER BY open_ts", (tf,)).fetchall()
                if tf else conn.execute(q + " ORDER BY open_ts").fetchall())
        conn.close()
        scope = f" {label_for(tf)}" if tf else ""
        done = set()
        if os.path.exists(PATHS_DONE):
            with open(PATHS_DONE) as f:
                done = {ln.strip() for ln in f if ln.strip()}
        todo = [m for m in mkts if _market_key(m[0], m[1], m[2]) not in done]
        if not todo:
            tg(f"✅ all {len(mkts)}{scope} markets already pulled — sending")
            send_paths_files(tf)
            return
        tg(f"⏳ pulling{scope} paths: {len(todo)} markets left of {len(mkts)} "
           f"(~{max(1, len(todo) * 7 // 600)} min). Saved as it goes — "
           f"safe to restart, just /exportpaths again.")
        new_file = not os.path.exists(PATHS_CSV)
        got = empty = 0
        for i, (asset, mtf, open_ts, close_ts) in enumerate(todo, 1):
            if _paths_pause.is_set():
                tg(f"⏸ paths paused at {i - 1}/{len(todo)} · progress saved\n"
                   f"/resumepaths to continue · /sendpaths to send what's done")
                return
            toks = resolve_tokens(asset, mtf, open_ts)
            rows = []
            if toks:
                for token_dir, tok in (("UP", toks[0]), ("DOWN", toks[1])):
                    for (t, p) in fetch_price_history(tok, open_ts, close_ts):
                        rows.append([asset, mtf, open_ts, token_dir, t,
                                     t - open_ts, round(p, 2)])
                    time.sleep(0.1)
            _market_cache.pop((asset, mtf, open_ts), None)   # keep memory flat
            with _paths_io_lock:
                with open(PATHS_CSV, "a", newline="") as f:
                    w = csv.writer(f)
                    if new_file:
                        w.writerow(PATHS_HEADER)
                        new_file = False
                    w.writerows(rows)
                with open(PATHS_DONE, "a") as f:
                    f.write(_market_key(asset, mtf, open_ts) + "\n")
            got += 1 if rows else 0
            empty += 0 if rows else 1
            if i % 1000 == 0:
                tg(f"⏳ paths {i}/{len(todo)} · {got} with data · {empty} empty")
        tg(f"✅{scope} paths done · {got} markets with data · {empty} empty — sending")
        send_paths_files(tf)
    except Exception as e:
        log.error(f"[EXPORT] {e}")
        tg(f"⚠️ path export stopped: {e} — /exportpaths resumes it")
    finally:
        _export_lock.release()


def send_paths_files(tf=None):
    """Gzip the paths CSV into parts under Telegram's limit and send each.
    Each part is a complete .csv.gz with its own header."""
    if not os.path.exists(PATHS_CSV):
        tg("no paths file yet — run /exportpaths")
        return
    parts, part_no = [], 0
    with _paths_io_lock:
        with open(PATHS_CSV, newline="") as src:
            header = src.readline()
            out = gz = None
            tf_col = PATHS_HEADER.index("tf")
            for line in src:
                if tf and line.split(",")[tf_col] != str(tf):
                    continue
                if gz is None or out.tell() >= TG_PART_BYTES:
                    if gz:
                        gz.close(); out.close()
                    part_no += 1
                    path = os.path.join(EXPORT_DIR,
                                        f"favdip_paths{'_' + label_for(tf) if tf else ''}"
                                        f"_part{part_no}.csv.gz")
                    out = open(path, "wb")
                    gz = gzip.GzipFile(fileobj=out, mode="wb")
                    gz.write(header.encode())
                    parts.append(path)
                gz.write(line.encode())
            if gz:
                gz.close(); out.close()
    if not parts:
        tg("no paths pulled for that timeframe yet" if tf
           else "paths file is empty so far")
        return
    for n, path in enumerate(parts, 1):
        try:
            with open(path, "rb") as f:
                r = requests.post(
                    f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendDocument",
                    data={"chat_id": TELEGRAM_CHAT_ID,
                          "caption": f"paths part {n}/{len(parts)}"},
                    files={"document": (os.path.basename(path), f,
                                        "application/gzip")},
                    timeout=300)
            if r.status_code != 200:
                tg(f"⚠️ part {n} upload failed ({r.status_code})")
        except Exception as e:
            tg(f"⚠️ part {n} upload failed: {e}")
        finally:
            try:
                os.remove(path)
            except Exception:
                pass


def _parse_tf(s):
    s = s.strip().lower()
    return {"15": 15, "15m": 15, "60": 60, "1h": 60, "60m": 60,
            "240": 240, "4h": 240, "240m": 240}.get(s)


def inverse_stats_text():
    inv, fav = db_scoreboard("inv_trades"), db_scoreboard("trades")
    if inv["n"] == 0:
        return ("🔄 <b>INVERSE · PAPER</b>\nno settled inverse trades yet "
                "(started with this update)")
    lines = [f"🔄 <b>INVERSE · PAPER</b>  (fills at the other side's real ask)",
             f"{inv['n']} trades · {inv['wr']:.1f}% win",
             f"hold {money(inv['hold'])} · ladder {money(inv['pnl'])}", "━━━━━━━━━━"]
    for tf, d in sorted(inv["by_tf"].items()):
        n = d["n"]
        lines.append(f"<b>{label_for(tf)}</b> {n} · {d['w'] / n * 100:.0f}% win · "
                     f"avg @{d['px'] / n:.0f}¢\n  hold {money(d['hold'])} "
                     f"({d['hold'] / n / PAPER_STAKE * 100:+.1f}%/trade) · "
                     f"ladder {money(d['pnl'])}")
    lines.append("━━━━━━━━━━")
    lines.append(f"favorite (all time): hold {money(fav['hold'])} · "
                 f"ladder {money(fav['pnl'])}")
    return "\n".join(lines)


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
            # optional timeframe argument: "/export 60", "/exportpaths 15m", "1h", "4h"
            parts = t.split()
            t = parts[0].split("@")[0] if parts else ""
            arg_tf = _parse_tf(parts[1]) if len(parts) > 1 else None
            if len(parts) > 1 and arg_tf is None:
                tg(f"unknown timeframe '{parts[1]}' — use 15m, 1h or 4h")
                continue
            if t == "/istats":
                tg(inverse_stats_text())
            elif t == "/stats":
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
                                 peak_after=p.get("peak_bid", 0.0),
                                 kind=p.get("kind", "FAV"))
                            for p in pending]
                head = f"📊 <b>FAVORITE DIP status</b>\n{len(snap)} open"
                lines = []
                for p in snap:
                    ar = "↑" if p["direction"] == "UP" else "↓"
                    st = (f"banked ${p['banked']:.2f}" if p["banked"] > 0
                          else "no rungs yet")
                    pk = f" · peak {p['peak_after']:.0f}¢" if p["peak_after"] else ""
                    lines.append(f"{'INV ' if p['kind'] == 'INV' else ''}"
                                 f"{ASSET_EMOJI.get(p['asset'],'')}{p['asset']} "
                                 f"{label_for(p['tf'])} {ar} @{p['entry']:.0f}¢\n"
                                 f"  {st} · {p['left']:.0f} riding · "
                                 f"next {p['rung']:.0f}¢{pk}")
                tg(head + ("\n\n" + "\n".join(lines) if lines else "\n\nno open positions"))
            elif t == "/export":
                sfx = f"_{label_for(arg_tf)}" if arg_tf else ""
                for table, name in (("trades", "favdip_trades"),
                                    ("inv_trades", "favdip_inverse")):
                    text, n = build_trades_csv(table, arg_tf)
                    if text:
                        tg_document(f"{name}{sfx}.csv", text, f"{n} rows · {table}")
                    else:
                        tg(f"no rows in {table}{' for ' + label_for(arg_tf) if arg_tf else ''} yet")
            elif t in ("/exportpaths", "/resumepaths"):
                _paths_pause.clear()
                threading.Thread(target=export_paths_worker, args=(arg_tf,),
                                 daemon=True).start()
            elif t == "/pausepaths":
                if _export_lock.locked():
                    _paths_pause.set()
                    tg("⏸ pausing after the current market…")
                else:
                    tg("no path export running")
            elif t == "/sendpaths":
                threading.Thread(target=send_paths_files, args=(arg_tf,),
                                 daemon=True).start()
            elif t == "/help":
                tg("📖 <b>commands</b>  (add 15m / 1h / 4h to limit to one timeframe)\n"
                   "/stats — favorite scoreboard\n"
                   "/istats — inverse vs favorite, per timeframe\n"
                   "/status — open positions\n"
                   "/export [tf] — favorite + inverse trades as CSV\n"
                   "/exportpaths [tf] — pull both sides' price paths (resumable)\n"
                   "/pausepaths — pause the path export\n"
                   "/resumepaths [tf] — continue where it stopped\n"
                   "/sendpaths [tf] — send the paths pulled so far\n"
                   "/help — this list")
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
                        opp_tok = toks[1] if direction == "UP" else toks[0]
                        opp_ask = best_ask_cents(opp_tok)
                        opp_bid = best_bid_cents(opp_tok)
                        entry_bid = best_bid_cents(tok)
                        rid = db_insert(asset, tf, direction, open_ts, close_ts,
                                        ask, pk, opp_ask, opp_bid, entry_bid)
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
                                "peak_bid": ask, "min_bid": None,
                                "table": "trades", "kind": "FAV",
                                "step": RUNG_STEP_CENTS, "frac": LADDER_SELL_FRAC,
                            })
                        if INV_ENABLED and opp_ask and 0 < opp_ask < RUNG_CAP_CENTS:
                            inv_dir = "DOWN" if direction == "UP" else "UP"
                            inv_rid = db_insert_inv(rid, asset, tf, inv_dir, open_ts,
                                                    close_ts, opp_ask, opp_bid, ask,
                                                    entry_bid, pk)
                            inv_sh = PAPER_STAKE / (opp_ask / 100.0)
                            with pending_lock:
                                pending.append({
                                    "rid": inv_rid, "asset": asset, "tf": tf,
                                    "direction": inv_dir, "open_ts": open_ts,
                                    "close_ts": close_ts, "entry_ask": opp_ask,
                                    "peak_at_entry": pk, "token": opp_tok,
                                    "shares_total": inv_sh, "shares_left": inv_sh,
                                    "next_rung": min(opp_ask + INV_RUNG_STEP_CENTS,
                                                     RUNG_CAP_CENTS),
                                    "ladder_proceeds": 0.0, "ladder_sold": 0.0,
                                    "peak_bid": opp_ask, "min_bid": None,
                                    "table": "inv_trades", "kind": "INV",
                                    "step": INV_RUNG_STEP_CENTS,
                                    "frac": INV_LADDER_SELL_FRAC,
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
                if now >= s["close_ts"]:
                    continue
                bid = best_bid_cents(s["token"])
                if bid is None:
                    continue
                if bid > s.get("peak_bid", 0.0):
                    s["peak_bid"] = bid
                if s.get("min_bid") is None or bid < s["min_bid"]:
                    s["min_bid"] = bid
                if s["shares_left"] < 1:
                    continue
                sold_this_poll = 0.0
                proceeds_this_poll = 0.0
                while bid >= s["next_rung"] and s["shares_left"] >= 1:
                    at_cap = s["next_rung"] >= RUNG_CAP_CENTS
                    sell_shares = s["shares_left"] * s.get("frac", LADDER_SELL_FRAC)
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
                    s["next_rung"] = min(s["next_rung"] + s.get("step", RUNG_STEP_CENTS),
                                         RUNG_CAP_CENTS)
                is_inv = s.get("kind") == "INV"
                if sold_this_poll > 0 and (not is_inv or INV_SEND_EACH):
                    tg(f"🪜 <b>{'INV ' if is_inv else ''}{ASSET_EMOJI.get(s['asset'],'')}{s['asset']} "
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
                                   s["ladder_proceeds"], 0,
                                   s.get("peak_bid"), s.get("min_bid"),
                                   s.get("table", "trades"))
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
                           round(s["ladder_proceeds"], 4), round(hold_pnl, 4),
                           s.get("peak_bid"), s.get("min_bid"),
                           s.get("table", "trades"))
                with pending_lock:
                    s in pending and pending.remove(s)
                if s.get("kind") == "INV":
                    if INV_SEND_EACH:
                        tg(f"{'✅' if won else '❌'} INV {s['asset']} "
                           f"{label_for(s['tf'])} @{s['entry_ask']:.0f}¢ · "
                           f"hold {money(hold_pnl)} · ladder {money(pnl)}")
                    continue
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
       f"{'🔄 inverse ON: each dip also buys the other side at its real ask · /istats' + chr(10) if INV_ENABLED else ''}"
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
