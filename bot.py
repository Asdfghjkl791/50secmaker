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
# Safety: starts with live OFF · stake capped by MAX_STAKE · daily loss stop · balance floor · max open trades · one trade per rule per market · skips when price or Polymarket data is stale · pauses after 3 order errors in a row.
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
                 conf=None, trol=False, lc=False, cap=10, live=False, bc=None, early=False, fair2=None, gap2=None, follow=None,
                 lc_min=None, opp_max=None, same_min=None, same_max=None, first_age=None, bps_min=None,
                 fade=False, fmin=None, fmax=None, dip=None, flat=None, persist=None):
        # Nov 19 additions (all optional, None/False = not used, so the older rules behave exactly as before):
        #   fair=None      no fair-price test at all · fair="ad" = whichever TWAP fair (Deribit vol / our vol) scored better lately
        #   lc_min         other exchanges must move >= this many bp our way in the 0.5s after the jump (no R check)
        #   opp_max        at most this many earlier jumps the OTHER way in this market (0 = none: a clean first move)
        #   same_min/max   earlier jumps the SAME way in this market (same_max=0 = this is the first; same_min=1 = a second push)
        #   first_age      the first same-way jump must be at least this many seconds old
        #   bps_min        the jump itself must be at least this big (bp)
        #   fade           buy the side the jump went AGAINST (the side that just fell)
        #   fmin / fmax    our fair for the side we buy must be above fmin / below fmax (50 = the side is ahead / behind)
        #   dip / flat     (min_age, max_age, cents): vs our side's ask that long ago, the ask is down by >= cents / moved < cents
        #   persist        (min_age, max_age): the fair gap must also have been there at the previous look that long ago
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
    Rule("TROL", "BTC D-15TROL", "BTC", 15, 3, "tw_o", 5, 15, 95, R=True, trol=True, cap=40),
    Rule("L15", "BTC D-15L", "BTC", 15, 3, "tw_o", 8, 20, 90, left_max=600, cap=15),
    Rule("H4", "BTC H4-LS", "BTC", 240, 2, "tw_d", 10, 10, 30, hi_incl=False, R=True, cap=15),
    Rule("EH4C", "ETH H4-LS-C", "ETH", 240, 2, "tw_d", 10, 10, 30, hi_incl=False, R=True, conf="first", cap=10),
    # Nov 13 (paper): BTC 15m long shot from real-time early2 data. 2bp BTC jump, Binance-candle fair (Deribit vol) - ask >= 10c,
    # ask 10-30c, no R check, ask read at the jump. Held up even with the order book 2s after the jump.
    # Nov 17: narrowed to 15-25c. Paper Nov 13-17: 10-15c -$1,579 and 25-30c -$1,569 at $100, 15-25c +$1,930. Checked on separate
    # BTC 15m history Nov 5-13: 15-25c 47 tr 38% won +$23.32 ($100 +$1,782, 2s book +$10.32), Up and Down both positive.
    Rule("BLS15", "BTC D-15LS2 15-25c", "BTC", 15, 2, "bn_d", 10, 15, 25, early=True, cap=10),
    # Nov 14 (paper): LC5 + a second opinion. Same as live LC5, but the Binance-candle fair (Deribit vol) must ALSO be >= 5c above
    # the ask. On LC5's own live trades Nov 13-14 the "both agree" half made +$15.93, the "TWAP only" half -$4.00. Needs a fair test.
    Rule("LC5B", "ETH D5-LC both fairs", "ETH", 5, 2, "tw_d", 5, 30, 95, R=True, lc=True, cap=15, fair2="bn_d", gap2=5),
    # (Nov 17: TR5, P5T, EBC5 and ELS5 removed - all lost clearly on paper; P5O replaced P5 live)
    # (Nov 16: FB5, the ETH 5m follow-BTC long shot, removed - its profit was all Down bets in Saturday's selloff, lost every day since)
    # Nov 15 (paper): ETH 15m follow-BTC, both fairs agree. When BTC jumps 2bp, buy the ETH 15m side in BTC's direction at 30-90c if
    # the TWAP fair AND the Binance-candle fair (both our own vol, as in the worker's recorder) are >= 5c above the ask.
    # Worker alts data Nov 13-15 (book 1s after, limit +10c): 68 trades, 76% won, +$15.80 at $1, +$1,219 at $100, positive Fri/Sat/Sun.
    Rule("FB15B", "ETH 15m follow-BTC both fairs", "ETH", 15, 2, "tw_o", 5, 30, 90, cap=10, follow="BTC", fair2="bn_o", gap2=5),
    # Nov 15 (paper) long-shot candidates from the deep search on real-time data (combo recorder Nov 13-15 + BTC recorder Nov 5-12).
    # All limit +10c (never chase). Fair test starts when this file goes live.
    # LS5H: BTC 5m, TWAP fair (Deribit vol) >= 10c above, 20-40c. Hist 24 tr 62% won +$14.40 · recent 21 tr 57% won +$15.65 (both sides)
    Rule("LS5H", "BTC 5m LS high-win", "BTC", 5, 3, "tw_d", 10, 20, 40, cap=10),
    # LS5O: BTC 5m, TWAP fair (own vol) >= 5c above, 10-40c. Hist 80 tr 48% +$27.10 · recent 134 tr 39% +$23.27. Needs speed (2s book ~0)
    Rule("LS5O", "BTC 5m LS own-vol", "BTC", 5, 3, "tw_o", 5, 10, 40, cap=10),
    # LS15O: same on BTC 15m. Hist 43 tr 49% +$29.69 · recent 60 tr 35% +$5.17. Not speed-sensitive
    Rule("LS15O", "BTC 15m LS own-vol", "BTC", 15, 3, "tw_o", 5, 10, 40, cap=10),
    # E15LA / E15LB: ETH 15m long shots on the Binance-candle fair (held on data after Sat 1:15pm). Read the ask at once (early=True),
    # as in the recorder test. A: Deribit vol >= 10c, 10-30c (76 tr 34% +$28.04) · B: own vol >= 5c, 20-35c (111 tr 41% +$27.86)
    Rule("E15LA", "ETH 15m LS Binance fair A", "ETH", 15, 2, "bn_d", 10, 10, 30, early=True, cap=10),
    Rule("E15LB", "ETH 15m LS Binance fair B", "ETH", 15, 2, "bn_o", 5, 20, 35, early=True, cap=10),
    # Nov 16 (paper): P5O = P5 with the fair built on OUR measured volatility instead of Deribit's. It adapts by itself: when BTC is
    # wilder than options assume (real/Deribit vol 0.9x on Nov 5-12, 1.28x from Nov 13) it asks for more before buying.
    # Nov 5-13: +$2,088 at $100 (P5 +$3,423) · Nov 13-15: +$1,066 (P5 -$374) · worst day -$257 (P5 -$557) · 10 of 12 days up.
    Rule("P5O", "BTC Plain D5 own-vol", "BTC", 5, 3, "tw_o", 5, 30, 90, cap=40),
    # Nov 16 (paper): EBC15 = the 15m sibling of EBC5 on the Binance fair with our vol. Recorder Nov 13-15: 117 tr, 67% won, +$27.05
    # ($100 +$2,414), both halves, Up and Down · early2 Nov 1-4/12-13: 119 tr, 57% won at 45c, +$16.81, 5 of 6 days up.
    Rule("EBC15", "ETH D15-BC own-vol", "ETH", 15, 2, "bn_o", 5, 30, 90, bc=1.0, early=True, cap=10),
    # Nov 17 (paper): the LS5H long-shot recipe on 1h and 4h markets - fair (Deribit vol) >= 10c above, 20-40c, limit +10c.
    # 1h settles on the Binance candle -> Binance fair; 4h settles on the Chainlink TWAP -> TWAP fair. Will fire rarely.
    Rule("LS1HB", "BTC 1h LS high-win", "BTC", 60, 2, "bn_d", 10, 20, 40, early=True, cap=10),
    Rule("LS1HE", "ETH 1h LS high-win", "ETH", 60, 2, "bn_d", 10, 20, 40, early=True, cap=10),
    Rule("LS4HB", "BTC 4h LS high-win", "BTC", 240, 2, "tw_d", 10, 20, 40, early=True, cap=10),
    Rule("LS4HE", "ETH 4h LS high-win", "ETH", 240, 2, "tw_d", 10, 20, 40, early=True, cap=10),
    # Nov 17 (paper): own-volatility long shots for 1h and 4h, using our volatility over the market's own length
    # (last 1 hour for 1h markets, last 4 hours for 4h) instead of Deribit's - the version that adapts to wild vs calm markets.
    Rule("LV1HB", "BTC 1h LS long-vol", "BTC", 60, 2, "bn_l", 5, 10, 40, early=True, cap=10),
    Rule("LV1HE", "ETH 1h LS long-vol", "ETH", 60, 2, "bn_l", 5, 10, 40, early=True, cap=10),
    Rule("LV4HB", "BTC 4h LS long-vol", "BTC", 240, 2, "tw_l", 5, 10, 40, early=True, cap=10),
    Rule("LV4HE", "ETH 4h LS long-vol", "ETH", 240, 2, "tw_l", 5, 10, 40, early=True, cap=10),
    # ── Nov 19 (paper): the rules found on Nov 18. Numbers are from the data they were FOUND on, so expect less on paper. ──
    # All limit +10c. "clean" = few or no earlier jumps the other way in this market (whipsaw markets are where the old rules lose).
    # P5A: P5 with the fair that has been more accurate over the last 24h of settled markets (Deribit vol or our vol), clean moves only.
    #      Nov 5-17: 556 tr, 76% won, +$47.84 at $1 (2s book), +$6,006 at $100, 11 of 13 days up (P5 +$23, P5O +$38 over the same days).
    Rule("P5A", "BTC 5m adaptive clean", "BTC", 5, 3, "ad", 5, 30, 90, opp_max=1),
    # M5: BTC 5m near 50c. Own-vol TWAP fair >= 3c above, other exchanges confirm >= 0.5bp, NO earlier jump the other way.
    #      Nov 5-12: 45 tr 78% won · Nov 13-17: 66 tr 79% won · +$19.50 at $1 (2s), +$2,344 at $100.
    Rule("M5", "BTC 5m mid clean", "BTC", 5, 3, "tw_o", 3, 45, 65, lc_min=0.5, opp_max=0),
    # LS5C: LS5O + first clean jump (first jump its way, at most one the other way). 80 tr, 57.5% won at ~30c, +$28.55 at $1 (2s).
    Rule("LS5C", "BTC 5m LS first clean", "BTC", 5, 3, "tw_o", 5, 10, 40, same_max=0, opp_max=1),
    # S15: BTC 15m. On 15m the FIRST jump is noise; the second push the same way (>=10s later, <=1 jump against) is the signal.
    #      Binance fair (our vol) >= 5c above, 40-80c. Oct 29-Nov 17: 418 tr, 74% won, +$40 at $1 (2s), +$4,858 at $100, 3 periods.
    Rule("S15", "BTC 15m second push", "BTC", 15, 3, "bn_o", 5, 40, 80, same_min=1, first_age=10, opp_max=1),
    # LL15: BTC 15m late long shot. Jump toward the cheap side with <= 4.5 min left, 20-35c, no fair test.
    #      Oct 29-Nov 17: 155 tr, 43% won at 27c, +$41.80 at $1 (2s), +$5,098 at $100, 3 periods.
    Rule("LL15", "BTC 15m late long shot", "BTC", 15, 3, None, 0, 20, 35, left_max=270),
    # E5S: ETH 5m. Jump >= 3bp and other exchanges follow >= 1bp within 0.5s, 30-95c, no fair test.
    #      early2 Nov 1-13: 273 tr 66% · recorder Nov 13-17: 302 tr 76% won, +$30 at $1 (2s), +$2,211 at $100.
    Rule("E5S", "ETH 5m strong confirm", "ETH", 5, 2, None, 0, 30, 95, bps_min=3, lc_min=1.0, early=True),
    Rule("ELS5", "ETH 5m LS strong confirm", "ETH", 5, 2, None, 0, 20, 40, bps_min=3, lc_min=0.5, early=True),
    # ^ ELS5 (added Nov 19, fair test from then): E5S's long-shot cousin. Recorder, cautious price: Nov 13-15 139 tr 45% won +$26.15 at $1,
    #   Nov 16-19 80 tr 48% won +$14.44. Older data (weaker stand-in confirm) about break-even, so unproven.
    # LC5K: live LC5 exactly, plus the clean check (<= 1 earlier ETH jump the other way). Recorder Nov 13-18: LC5 +$1,081 at $100,
    #      with the check +$2,250 on half the trades, 6 of 6 days up. Compare it with LC5 day by day.
    Rule("LC5K", "ETH D5-LC clean", "ETH", 5, 2, "tw_d", 5, 30, 95, R=True, lc=True, cap=15, opp_max=1),
    # E5A: ETH 5m high-win. Adaptive fair >= 10c above, others confirm, clean. Recorder Nov 13-18: 86 tr, 78% won, +$16.41 at $1 (2s).
    Rule("E5A", "ETH 5m adaptive high-win", "ETH", 5, 2, "ad", 10, 30, 95, lc_min=0.1, opp_max=1, early=True),
    # R15: ETH 15m early reversal. In the first 3 minutes buy the side the jump went AGAINST when it is 20-60c, its ask fell >= 3c
    #      in the last 30-90s and the Binance fair (our vol) still puts it >= 5c above the ask. Low win rate, big payoff.
    #      Tracker Oct 3-Nov 5: 915 tr 35% won +$9,880 at $100 · recorder Nov 13-18 (never searched): 77 tr 51% won, +$29.91 at $1.
    Rule("R15", "ETH 15m early reversal", "ETH", 15, 2, "bn_o", 5, 20, 60, fade=True, fmax=50, left_min=720, left_max=876,
         dip=(30, 90, 3), early=True),
    Rule("R15C", "ETH 15m early reversal 40-60c", "ETH", 15, 2, "bn_o", 5, 40, 60, fade=True, fmax=50, left_min=720, left_max=876,
         dip=(30, 90, 3), early=True),
    # The 1h / 4h rules below were found on Aug-Oct tracker data and were FLAT on the recorder's Nov 13-17 (few trades): watch only.
    # L1H: BTC 1h, minutes 30-50, the side that is ahead, long-vol fair >= 5c above now and at the previous look 45-150s ago.
    Rule("L1H", "BTC 1h leader underpriced", "BTC", 60, 2, "bn_l", 5, 20, 80, fmin=50, left_min=600, left_max=1800,
         persist=(45, 150), early=True),
    # D4H: BTC 4h favourite dip. Leader at 75-95c, its ask fell >= 3c over the last 6-12 min, long-vol fair still >= 3c above.
    Rule("D4H", "BTC 4h favourite dip", "BTC", 240, 2, "tw_l", 3, 75, 95, fmin=50, dip=(360, 720, 3), early=True),
    # F4H: ETH 4h steady favourite. Leader at 75-95c, ask moved < 3c over the last 6-12 min, long-vol fair >= 8c above.
    Rule("F4H", "ETH 4h steady favourite", "ETH", 240, 2, "tw_l", 8, 75, 95, fmin=50, flat=(360, 720, 3), early=True),
]
RULE = {r.code: r for r in RULES}
PLAN = {a: sorted({r.tf for r in RULES if r.asset == a}) for a in ASSETS}
AD_KEYS = sorted({(r.asset, r.tf, r.trig) for r in RULES if r.fair == "ad"})          # what the adaptive scorer has to follow
LOOK_KEYS = {(r.asset, r.tf, r.trig) for r in RULES if r.dip or r.flat or r.persist}  # markets whose earlier looks we keep

# ── shared state ─────────────────────────────────────────────────────────────────
lock = threading.RLock()
px = {a: {} for a in ASSETS}                 # px[asset][venue] = deque((t, mid))
px1s = {a: deque(maxlen=4000) for a in ASSETS}
px60 = {a: deque(maxlen=720) for a in ASSETS}           # one Binance price a minute, 12h back: long-window volatility for 1h / 4h markets
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
JH = {}                                      # (asset, trig) -> deque((t0, direction)): every jump, for the "clean move" rules
LOOKS = {}                                   # (asset, tf, o) -> deque((t0, direction, up ask, down ask, fairs)): what a market looked like at each jump
AD = {}                                      # (asset, tf) -> {"pick", "tw_d", "tw_o", "n", "ts"}: which TWAP fair scored better over the last 24h
AD_DEFAULT = "tw_d"                          # until 40 settled samples exist, the adaptive rules use the Deribit-vol fair (as tested)


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
    for col in ("bk_age REAL", "a0_ts REAL", "a25_ts REAL", "t_build REAL", "ft_c REAL", "ft_m REAL", "ft_n INTEGER",
                "volr REAL", "j1h INTEGER", "ar1h REAL",
                "fk TEXT", "n_same INTEGER", "n_opp INTEGER",
                "q_cost1 REAL", "q_sh1 REAL", "q_cost100 REAL", "q_sh100 REAL", "q_px REAL", "q_pnl1 REAL", "q_pnl100 REAL",   # old 1s-book paper price
                "t_hdr REAL", "pm_lag REAL"):     # Nov 19: which fair was used, earlier jumps same way / other way
        try:
            dbx(f"ALTER TABLE trades ADD COLUMN {col}")
        except sqlite3.OperationalError:
            pass
    dbx("""CREATE TABLE IF NOT EXISTS copiers (id INTEGER PRIMARY KEY AUTOINCREMENT, trade_id INTEGER, ts REAL, wallet TEXT, name TEXT,
        delay REAL, size REAL, price REAL)""")
    dbx("CREATE TABLE IF NOT EXISTS moves (t0 REAL, asset TEXT, trig INTEGER, feed TEXT, bps REAL, fut_lag REAL)")
    dbx("CREATE TABLE IF NOT EXISTS rec (id INTEGER PRIMARY KEY AUTOINCREMENT, t0 REAL, asset TEXT, trig INTEGER, tf INTEGER, o INTEGER, up INTEGER, data BLOB)")
    dbx("CREATE INDEX IF NOT EXISTS rec_t0 ON rec (t0)")
    dbx("CREATE TABLE IF NOT EXISTS outcomes (asset TEXT, tf INTEGER, o INTEGER, outcome TEXT, PRIMARY KEY (asset, tf, o))")
    dbx("CREATE TABLE IF NOT EXISTS stats (day TEXT, code TEXT, k TEXT, n INTEGER, PRIMARY KEY (day, code, k))")
    dbx("CREATE TABLE IF NOT EXISTS kv (k TEXT PRIMARY KEY, v TEXT)")
    dbx("CREATE TABLE IF NOT EXISTS ftrack (t0 REAL, feed TEXT, bps REAL, ft10 REAL)")
    dbx("CREATE INDEX IF NOT EXISTS ftrack_t0 ON ftrack (t0)")


_kvc = {}


def kv_get(k, d=None):
    hit = _kvc.get(k)
    if hit and time.time() - hit[0] < (30 if k in HOT_KV else 2):   # hot settings are refreshed in the background (kv_worker)
        return hit[1] if hit[1] is not None else d
    r = dbq("SELECT v FROM kv WHERE k=?", (k,))
    v = r[0]["v"] if r else None
    _kvc[k] = (time.time(), v)
    return v if v is not None else d


def kv_set(k, v):
    dbx("INSERT OR REPLACE INTO kv (k, v) VALUES (?,?)", (k, str(v)))
    _kvc[k] = (time.time(), str(v))


HOT_KV = ("live_on", "live_rules", "stake", "paused", "quiet", "quiet_hours", "half_hours", "rule_loss")


def kv_worker():
    """Nov 14 speed-up: keep the settings an order needs in memory, so a trade never waits on the database"""
    while True:
        try:
            rows = {r["k"]: r["v"] for r in dbq("SELECT k, v FROM kv WHERE k IN (%s)" % ",".join("?" * len(HOT_KV)), HOT_KV)}
            now = time.time()
            for k in HOT_KV:
                _kvc[k] = (now, rows.get(k))
        except Exception as e:
            _err("kv_worker", e)
        time.sleep(1)


RISK = {"ts": 0.0, "today": 0.0, "open": 0, "by_code": {}}


MIN_ORDER = 1.0      # Polymarket's smallest market buy ($)


def quiet_hours(key="quiet_hours"):
    """(start_hour, end_hour) in Toronto time, or None. quiet_hours: 5-minute rules trade on paper only (/quiethours).
    half_hours: 5-minute rules trade at half stake (/halfhours)"""
    v = (kv_get(key, "") or "").strip()
    try:
        a, b = v.split("-")
        a, b = int(a), int(b)
        return (a, b) if 0 <= a <= 23 and 1 <= b <= 24 and a != b else None
    except Exception:
        return None


def in_quiet_hours(r, t=None, key="quiet_hours"):
    qh = quiet_hours(key)
    if not qh or r.tf != 5:
        return False
    h = datetime.fromtimestamp(t or time.time(), TZ).hour
    a, b = qh
    return (a <= h < b) if a < b else (h >= a or h < b)


def rule_loss_cap():
    try:
        return max(0.0, float(kv_get("rule_loss", "0") or 0))
    except Exception:
        return 0.0


def road(a, t0):
    """road conditions at the moment of a trade, saved with it so 'slow down' levels can be tested later:
    volr = our measured volatility / Deribit's (above 1 = wilder than options assume) · j1h = BTC 3bp jumps in the last hour ·
    ar1h = size of the coin's move over the last hour (bp)"""
    volr = j1h = ar1h = None
    try:
        so, sd = sigma(a), sigma_iv(a, 5)
        volr = round(so / sd, 3) if (so and sd) else None
        j1h = sum(1 for (ts, f) in list(FT) if t0 - 3600 <= ts <= t0)
        pts = list(px1s[a])
        if pts and pts[-1][0] - pts[0][0] >= 3000:
            old = min(pts, key=lambda p: abs(p[0] - (t0 - 3600)))
            ar1h = round(abs(pts[-1][1] / old[1] - 1) * 1e4, 1)
    except Exception as e:
        _err("road", e)
    return volr, j1h, ar1h


def risk_worker():
    """Nov 14 speed-up: today's settled live result + open live trades, recounted every second off the trading path"""
    while True:
        try:
            t_day = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
            td = dbq("SELECT COALESCE(SUM(pnl),0) s FROM trades WHERE mode='LIVE' AND status='SETTLED' AND t0 >= ?", (t_day,))[0]["s"]
            op = dbq("SELECT COUNT(*) n FROM trades WHERE mode='LIVE' AND status='HOLDING' AND t0 >= ?", (t_day - 86400,))[0]["n"]
            bc = {x["code"]: float(x["s"] or 0) for x in dbq(
                "SELECT code, SUM(pnl) s FROM trades WHERE mode='LIVE' AND status='SETTLED' AND t0 >= ? GROUP BY code", (t_day,))}
            RISK.update(ts=time.time(), today=float(td or 0), open=int(op or 0), by_code=bc)
        except Exception as e:
            _err("risk_worker", e)
        time.sleep(1)


def keepalive_worker():
    """Nov 14 speed-up: touch Polymarket's order server every few seconds so the connection is already open when an order goes"""
    while True:
        try:
            if live_on() and POLY_PRIVATE_KEY and _clob is not None:
                fn = getattr(_clob, "get_ok", None) or getattr(_clob, "get_server_time", None)
                if fn is None:
                    return                          # this client version has no cheap call: nothing to keep warm
                fn()
        except Exception as e:
            _err("keepalive", e)
        time.sleep(4)


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
    return kv_get("quiet", "1") == "1"          # default: no per-trade messages, a table every 30 min instead (/quiet off to get them)


# ── Telegram ─────────────────────────────────────────────────────────────────────
def tg(msg, pre=False):
    try:
        data = {"chat_id": TG_CHAT, "text": msg[:4000], "disable_web_page_preview": "true"}
        if pre:                                   # fixed-width font so table columns line up
            import html
            data.update(text="<pre>" + html.escape(msg[:3900]) + "</pre>", parse_mode="HTML")
        requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage", data=data, timeout=15)
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


def fast_post(c, order, ot, tim=None):
    try:
        import py_clob_client_v2.client as cm
        owner = c.creds.api_key or ""
        payload = (cm.order_to_json_v2(order, owner, ot, False, False) if cm._is_v2_order(order)
                   else cm.order_to_json_v1(order, owner, ot, False, False))
        ser = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
        headers = c._l2_headers("POST", cm.POST_ORDER, body=payload, serialized_body=ser)
        if tim is not None:
            tim["hdr"] = time.time()               # everything up to here is our own work; after it we wait for Polymarket
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
            resp = fast_post(clob(), order, OrderType.FAK, tim) or {}
        except Exception as e:
            resp = {"success": False, "errorMsg": str(e)[:200]}
        t2 = time.time()
    tim.update(build=t1 - t0, sent=t1, resp=t2, hdr=(tim["hdr"] - t1) if tim.get("hdr") else None)
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


def _run_ws(name, url, on_msg, subs=None, ping=None, ping_every=15, timeout=30, retry=5):
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
        time.sleep(retry)


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
            if not px60[a] or now - px60[a][-1][0] >= 60:
                px60[a].append((now, p))
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
                if q:
                    cl_gaps[a].append((now, now - q[-1][1]))
                q.append((ts, now, v))
                _push(a, "cl", v, now, every=0)
    # Nov 14: two connections + quick reconnect (before: 30s silence + 5s pause, price up to ~35s old).
    # Nov 16: the feed comes in bursts with normal pauses up to ~11s, so treat 15s of silence as dead (5s caused needless reconnects).
    for i in (1, 2):
        threading.Thread(target=_run_ws, args=(f"chainlink{i}", RTDS, on, subs, "PING", 5, 15, 0.5), daemon=True).start()
    while True:
        time.sleep(3600)


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
        try:                                       # Nov 19: how far behind Polymarket's own clock each book message arrives (seconds)
            st["pm_lag"] = st["pm_msg"] - float(m["timestamp"]) / 1000.0
        except Exception:
            pass
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


pm_gen = {"n": 0, "retired": set()}


def pm_conn(toks, gen, slot):
    """one Polymarket book connection for a fixed set of markets; reconnects at once if the server drops it (it does, every few minutes)"""
    fails = 0
    while gen not in pm_gen["retired"]:
        try:
            ws = websocket.create_connection(PM_WS, timeout=10)
            ws.settimeout(15)
            ws.send(json.dumps({"assets_ids": list(toks), "type": "market"}))
            lp = time.time()
            fails = 0
            while gen not in pm_gen["retired"]:
                if time.time() - lp > 10:
                    ws.send("PING")
                    lp = time.time()
                raw = ws.recv()
                if raw and raw[0] in "{[":
                    pm_handle(json.loads(raw))
            ws.close()
        except Exception as e:
            if gen in pm_gen["retired"]:
                return
            fails += 1
            st["pm_drops"] = st.get("pm_drops", 0) + 1
            if fails >= 3:
                _err("pm", e)
            time.sleep(0.05 if fails < 3 else 2)


def pm_worker():
    """keeps TWO book connections open (if one drops, the other keeps the prices fresh). When the list of markets changes,
    the new pair is opened first and the old pair is closed 3s later, so there is never a gap."""
    cur = None
    while True:
        try:
            with lock:
                toks = tuple(sorted(t for v in markets.values() for t in (v["up"], v["dn"])))
            if toks and toks != cur:
                old = pm_gen["n"]
                pm_gen["n"] += 1
                for slot in (0, 1):
                    threading.Thread(target=pm_conn, args=(toks, pm_gen["n"], slot), daemon=True).start()
                if cur is not None:
                    time.sleep(3)
                    pm_gen["retired"].add(old)
                cur = toks
            if cur:
                with lock:
                    keep = set(cur)
                    for t in [t for t in books if t not in keep]:
                        books.pop(t, None)
                        book_ts.pop(t, None)
        except Exception as e:
            _err("pm_worker", e)
        time.sleep(1)


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


def sigma_long(a, window):
    """Nov 16: our own volatility measured over the last `window` seconds from 1-minute prices (per-second units, like sigma()).
    sigma() looks at 15 minutes, right for 5m/15m markets; an hour or four of market needs a longer look back."""
    now = time.time()
    pts = [p for p in list(px60[a]) if p[0] >= now - window]
    r = [(math.log(y / x)) ** 2 for (t0, x), (t1, y) in zip(pts, pts[1:]) if 30 <= t1 - t0 <= 180 and x > 0 and y > 0]
    span = sum(t1 - t0 for (t0, x), (t1, y) in zip(pts, pts[1:]) if 30 <= t1 - t0 <= 180)
    if len(r) < 20 or span < 0.5 * window:
        return None
    return max(2e-5, math.sqrt(sum(r) / span))


def seed_px60():
    """fill the 1-minute price history from Binance at start-up, so the long-window volatility works at once after a restart"""
    for a in ASSETS:
        try:
            j = requests.get(KLINES, params={"symbol": SYM[a].upper(), "interval": "1m", "limit": 300}, timeout=10).json()
            rows = [(float(k[6]) / 1000, float(k[4])) for k in j if isinstance(k, list)][:-1]      # (close time, close), finished candles
            if rows and not px60[a]:
                px60[a].extend(rows)
            elif rows:
                first = px60[a][0][0]
                old = [x for x in rows if x[0] < first - 30]
                cur = list(px60[a])
                px60[a].clear()
                px60[a].extend(old + cur)
        except Exception as e:
            _err("seed_px60", e)


def sigma_iv(a, tf=None):
    d = iv50 if (a == "BTC" and tf in (5, 15)) else (ivs.get(a) or {})
    if not d.get("iv") or time.time() - d["ts"] > 600:
        return None
    return d["iv"] / 100 / math.sqrt(365 * 86400)


def _rev(q):
    """newest-first view of a deque that other threads keep appending to (iterating it live can raise 'deque mutated')"""
    for _ in range(3):
        try:
            return list(reversed(q))
        except RuntimeError:
            continue
    return list(reversed(list(q)))


def last(a, venue, t=None):
    q = px[a].get(venue)
    if not q:
        return None
    if t is None:
        return q[-1][1]
    if q[-1][0] <= t:
        return q[-1][1]
    for tt, p in _rev(q):
        if tt <= t:
            return p
    return None


def cl_now(a, t):
    """Chainlink price brought up to time t with Binance's move since that tick arrived"""
    x = None
    for item in _rev(cl[a]):
        if item[1] <= t:
            x = item
            break
    if not x:
        return None
    ts, rt, v = x
    b0, b1 = last(a, "vis", rt), last(a, "vis", t)
    return v * b1 / b0 if b0 and b1 else v


def cl_now_1s(a, t):
    """the BTC 5m/15m research (50secmaker) brought Chainlink up to now with Binance's 1-SECOND samples, so a jump in the last
    second was usually not in its fair yet. The BTC 5m/15m rules' edges were measured on that fair, so we compute it the same way."""
    x = None
    for item in _rev(cl[a]):
        if item[1] <= t:
            x = item
            break
    if not x:
        return None
    ts, rt, v = x
    s = [p for p in list(px1s[a]) if p[0] <= t]
    b0 = next((p for tt, p in reversed(s) if tt <= rt), None)
    return v * s[-1][1] / b0 if (s and b0) else v


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
    if tf >= 60:                                     # 1h / 4h: also a fair on our volatility over the last hour / four hours ("_l")
        vols["l"] = sigma_long(a, tf * 60)
    pb, pc = last(a, "vis", t), (cl_now_1s(a, t) if (a == "BTC" and tf in (5, 15)) else cl_now(a, t))
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
    if a == "BTC" and abs(bps) >= 3:                                        # BTC 5m/15m rules: 3bp jump on any Binance feed (as in their research)
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


CL_STALE = 20.0       # seconds: TWAP-fair rules skip signals when the last Chainlink price is older than this
                      # Nov 16: the feed arrives in bursts (about 1 price/s on average, but 637 gaps >3s an hour, longest ~11s)
                      # -> 10s skipped ~5% of normal signals. 20s still catches real outages (the 26-35s one on Nov 14).
ENTRY_DELAY = 0.30     # seconds after a 2bp jump at which the ETH / 1h / 4h rules read the ask (matches their research data)


def jump_hist(a, trig, o, t0, sg):
    """earlier jumps of this coin inside this market: (how many the same way, how many the other way, time of the first same-way one)"""
    with lock:
        q = [x for x in JH.get((a, trig), ()) if o <= x[0] < t0]
    same = [t for t, g in q if g == sg]
    return len(same), len(q) - len(same), (min(same) if same else None)


def look_back(a, tf, o, t0, lo, hi, sg, up):
    """the latest earlier look at this market that is at least lo seconds old (sg: only jumps that way; None = any jump) and has an ask
    for the side we want; None if that look is older than hi seconds. Same lookup the research used on the recorder."""
    with lock:
        q = list(LOOKS.get((a, tf, o), ()))
    for x in reversed(q):
        if x[0] <= t0 - lo and (sg is None or x[1] == sg) and (x[2] if up else x[3]) is not None:
            return x if t0 - x[0] <= hi else None
    return None


def eval_market(a, tf, o, m, up, t0, feed, bps, fu, m10, m2, rules, delay):
    try:
        if delay:
            time.sleep(max(0.0, t0 + delay - time.time()))
        if time.time() - st["pm_msg"] > 3:            # no Polymarket data for 3s: prices can't be trusted, skip (paper too)
            bump("ALL", "pm_stale")
            return
        asks = {}

        def side_ask(u):                               # best ask of the UP / DOWN token, read once per market per jump
            if u not in asks:
                tk = m["up"] if u else m["dn"]
                la = asks_of(tk, 1)
                ts = time.time()
                asks[u] = (la[0][0], ts, round(ts - book_ts.get(tk, 0), 3)) if la else None
            return asks[u]

        if side_ask(up) is None and not any(r.fade for r in rules):
            return
        left = o + tf * 60 - t0
        sg = 1 if up else -1
        cl_old = not cl[a] or time.time() - cl[a][-1][1] > CL_STALE
        hist = {}
    except Exception as e:
        _err("eval_market", e)
        return
    for r in rules:
        try:                                           # Nov 19: one rule's error can no longer stop the rules after it
            if r.tf != tf or (r.code, a, tf, o) in done:
                continue
            if r.bps_min is not None and abs(bps) < r.bps_min:
                continue
            rup = (not up) if r.fade else up           # fade rules buy the side the jump went against
            fk = AD.get((a, tf), {}).get("pick", AD_DEFAULT) if r.fair == "ad" else r.fair
            tested = fk is not None
            if not tested:                             # no fair test: still store a fair for the record
                fk = "tw_o" if a == "BTC" else "tw_d"
            f = fu.get(fk)
            if tested:
                if f is None:
                    continue
                if fk.startswith("tw") and cl_old:
                    bump(r.code, "cl_stale")             # Nov 14: Chainlink feed down -> the TWAP fair is guesswork, skip (paper too)
                    continue
            sa = side_ask(rup)
            if sa is None:
                continue
            a0, a0_ts, bk_age = sa
            fv = None if f is None else (f if rup else 100 - f)
            gap = None if fv is None else fv - a0
            if not in_range(r, a0) or (tested and gap < r.gap):
                continue
            if tested and ((r.fmin is not None and not fv > r.fmin) or (r.fmax is not None and not fv < r.fmax)):
                continue
            if r.fair2:                                # second fair price must agree too (paper rule LC5B)
                f2 = fu.get(r.fair2)
                if f2 is None or (f2 if rup else 100 - f2) - a0 < r.gap2:
                    continue
            if (r.left_max is not None and left > r.left_max) or (r.left_min is not None and left < r.left_min):
                continue
            if r.conf == "filter" and not (m10 is not None and m10 >= 2):
                continue
            if r.trol and not (m2 is not None and m2 <= 1.15):
                continue
            n_same = n_opp = None
            if r.opp_max is not None or r.same_min is not None or r.same_max is not None or r.first_age is not None:
                if r.trig not in hist:
                    hist[r.trig] = jump_hist(a, r.trig, o, t0, sg)
                n_same, n_opp, first = hist[r.trig]
                if (r.opp_max is not None and n_opp > r.opp_max) or (r.same_max is not None and n_same > r.same_max) \
                        or (r.same_min is not None and n_same < r.same_min) \
                        or (r.first_age is not None and (first is None or t0 - first < r.first_age)):
                    continue
            bad = False
            for kind, spec in (("dip", r.dip), ("flat", r.flat), ("persist", r.persist)):
                if not spec:
                    continue
                lk = look_back(a, tf, o, t0, spec[0], spec[1], None if r.fade else sg, rup)
                if lk is None:
                    bad = True
                    break
                pa = lk[2] if rup else lk[3]
                if kind == "dip":
                    bad = a0 - pa > -spec[2]
                elif kind == "flat":
                    bad = abs(a0 - pa) >= spec[2]
                else:
                    pf = lk[4].get(fk)
                    bad = pf is None or (pf if rup else 100 - pf) - pa < r.gap
                if bad:
                    break
            if bad:
                continue
            tok, opp = (m["up"], m["dn"]) if rup else (m["dn"], m["up"])
            ctx = dict(a=a, tf=tf, o=o, tok=tok, opp=opp, up=rup, side="UP" if rup else "DOWN", t0=t0, feed=feed, bps=bps, a0=a0,
                       fair=None if fv is None else round(fv, 2), gap=None if gap is None else round(gap, 2), left=round(left, 1),
                       m10=m10, m2=m2, cond=m.get("cond"), a0_ts=a0_ts, bk_age=bk_age, late=bool(delay), sg=sg, pm_lag=st.get("pm_lag"),
                       fk=fk if tested else None, n_same=n_same, n_opp=n_opp)
            threading.Thread(target=decide, args=(r, ctx), daemon=True).start()
        except Exception as e:
            _err("eval_" + r.code, e)


def in_range(r, ask):
    return ask >= r.lo and (ask <= r.hi if r.hi_incl else ask < r.hi)


REC_OFFS = (0.0, 0.25, 0.5, 1.0, 2.0)


def rec_capture(a, trig, feed, bps, t0):
    """light research recorder (Nov 13): for EVERY jump, every live market of that coin: all fair prices at the jump, other-exchange
    moves, and both sides' order books at 0 / 0.25 / 0.5 / 1 / 2 s. Same real-time numbers the trading uses. Never trades."""
    try:
        import zlib
        sg = 1 if bps > 0 else -1
        with lock:
            mk = [(k, dict(v)) for k, v in markets.items() if k[0] == a and k[2] <= t0 < k[2] + k[1] * 60]
        if not mk:
            return
        base = {"pm_lag0": round(st["pm_lag"], 3) if st.get("pm_lag") is not None else None, "bps": bps, "feed": feed, "m10": lead_mean(a, t0, -10, sg), "m2": lead_mean(a, t0, -2, sg),
                "vis0": last(a, "vis", t0), "sig": sigma(a), "sigl1": sigma_long(a, 3600), "sigl4": sigma_long(a, 14400), "iv": (ivs.get(a) or {}).get("iv"), "iv50": iv50.get("iv") if a == "BTC" else None}
        per = {}
        for (a_, tf, o), m in mk:
            fu = fairs(a, tf, o, t0)
            if a == "BTC" and tf in (5, 15):                           # also keep the tick-price version of the TWAP fair
                pc = cl_now(a, t0)
                k, _ = tw_strike(a, tf, o)
                fu["tw_tick_ref"] = round(pc / k * 1e4 - 1e4, 3) if (pc and k) else None
            k, src = tw_strike(a, tf, o)
            per[(tf, o)] = {"fair": fu, "left": round(o + tf * 60 - t0, 2), "k": k, "ksrc": src, "bn": (opens.get((a, tf, o)) or {}).get("bn"),
                            "up_tok": m["up"], "dn_tok": m["dn"], "s": {}}
        for off in REC_OFFS:
            time.sleep(max(0.0, t0 + off - time.time()))
            with lock:
                for (tf, o), d in per.items():
                    snap = {}
                    for side, tok in (("u", d["up_tok"]), ("d", d["dn_tok"])):
                        b = books.get(tok) or {}
                        snap[side + "a"] = sorted((p, round(z, 1)) for p, z in (b.get("asks") or {}).items() if p < 100)[:5]
                        snap[side + "b"] = sorted(((p, round(z, 1)) for p, z in (b.get("bids") or {}).items()), reverse=True)[:3]
                    d["s"][f"{off:g}"] = snap
        base.update(p05=lead_mean(a, t0, 0.5, sg), p1=lead_mean(a, t0, 1.0, sg), vis05=last(a, "vis", t0 + 0.5),
                    vis1=last(a, "vis", t0 + 1.0), vis2=last(a, "vis", t0 + 2.0), pm_age=round(time.time() - st["pm_msg"], 2),
                    pm_lag2=round(st["pm_lag"], 3) if st.get("pm_lag") is not None else None)
        for (tf, o), d in per.items():
            d.pop("up_tok"), d.pop("dn_tok")
            blob = zlib.compress(json.dumps({**base, **d}, separators=(",", ":")).encode())
            dbx("INSERT INTO rec (t0, asset, trig, tf, o, up, data) VALUES (?,?,?,?,?,?,?)", (t0, a, trig, tf, o, 1 if sg > 0 else 0, blob))
    except Exception as e:
        _err("rec", e)


def rec_outcome_worker():
    """market results for the recorder, and drop recorder rows older than 10 days"""
    n = 0
    while True:
        try:
            now = time.time()
            for x in dbq("SELECT DISTINCT r.asset, r.tf, r.o FROM rec r LEFT JOIN outcomes c ON c.asset=r.asset AND c.tf=r.tf AND c.o=r.o "
                         "WHERE c.outcome IS NULL AND r.o + r.tf*60 < ? AND r.o + r.tf*60 > ? LIMIT 40", (now - 60, now - 2 * 86400)):
                oc = outcome(x["asset"], x["tf"], x["o"])
                if oc:
                    dbx("INSERT OR REPLACE INTO outcomes (asset, tf, o, outcome) VALUES (?,?,?,?)", (x["asset"], x["tf"], x["o"], oc))
                time.sleep(0.3)
            n += 1
            if n % 60 == 0:
                dbx("DELETE FROM rec WHERE t0 < ?", (now - 10 * 86400,))
        except Exception as e:
            _err("rec_outcomes", e)
        time.sleep(60)


def ad_update(seen, last_id, now):
    """one scoring pass of the adaptive fair (see ad_worker)"""
    import zlib
    ocs = {(x["asset"], x["tf"], x["o"]): x["outcome"] for x in dbq("SELECT asset, tf, o, outcome FROM outcomes WHERE o > ? AND o < ?",
                                                                     (now - 27 * 3600, now))}
    for k in AD_KEYS:
        a, tf, trig = k
        for x in dbq("SELECT id, t0, o, up, data FROM rec WHERE id > ? AND t0 > ? AND t0 <= ? AND asset=? AND tf=? AND trig=? ORDER BY id",
                     (last_id[k], now - 26 * 3600, now, a, tf, trig)):
            last_id[k] = max(last_id[k], x["id"])
            kk = (x["o"], x["up"])
            if kk in seen[k] and seen[k][kk][0] <= x["t0"]:
                continue                               # only the first jump per market and side counts
            fr = json.loads(zlib.decompress(x["data"])).get("fair") or {}
            seen[k][kk] = (x["t0"], fr.get("tw_d"), fr.get("tw_o"))
        for kk in [kk for kk in seen[k] if kk[0] + tf * 60 < now - 26 * 3600]:
            seen[k].pop(kk, None)
        err = {"tw_d": [], "tw_o": []}
        for (o, up), (t_, fd, fo) in seen[k].items():
            end = o + tf * 60
            oc = ocs.get((a, tf, o))
            if oc not in ("UP", "DOWN") or not (now - 86400 <= end <= now):
                continue
            w = 1.0 if oc == "UP" else 0.0
            if fd is not None:
                err["tw_d"].append((fd / 100.0 - w) ** 2)
            if fo is not None:
                err["tw_o"].append((fo / 100.0 - w) ** 2)
        sc = {f: (sum(v) / len(v) if len(v) >= 40 else None) for f, v in err.items()}
        pick = "tw_o" if (sc["tw_d"] is not None and sc["tw_o"] is not None and sc["tw_o"] < sc["tw_d"]) else AD_DEFAULT
        AD[(a, tf)] = {"pick": pick, "tw_d": sc["tw_d"], "tw_o": sc["tw_o"], "n": min(len(err["tw_d"]), len(err["tw_o"])), "ts": now}


def ad_worker():
    """adaptive fair (Nov 19): for each market type an "ad" rule trades, score both TWAP fairs on the last 24h of SETTLED markets
    (first jump per market and side, squared error of the fair vs what happened) and use the one that was closer to the truth.
    It needs 40 settled samples of each; before that the Deribit-vol fair is used. Reads the recorder table, so it survives restarts."""
    seen = {k: {} for k in AD_KEYS}                    # (asset, tf, trig) -> {(o, up): (t0, Deribit-vol fair, own-vol fair)}
    last_id = {k: 0 for k in AD_KEYS}
    while True:
        try:
            ad_update(seen, last_id, time.time())
        except Exception as e:
            _err("ad_worker", e)
        time.sleep(30)


def ad_text():
    out = []
    for a, tf, trig in AD_KEYS:
        d = AD.get((a, tf))
        if not d:
            out.append(f"{a} {tf}m: starting up -> Deribit vol")
        elif d["tw_d"] is None or d["tw_o"] is None:
            out.append(f"{a} {tf}m: Deribit vol (only {d['n']} settled samples in 24h, needs 40)")
        else:
            out.append(f"{a} {tf}m: {'our vol' if d['pick'] == 'tw_o' else 'Deribit vol'} "
                       f"(error score: Deribit {d['tw_d']:.3f}, ours {d['tw_o']:.3f}, {d['n']} samples, lower = better)")
    return "\n".join(out)


def rec_export(all_=False):
    import zlib
    last_id = 0 if all_ else int(kv_get("rec_last_id", "0") or 0)
    rows = dbq("SELECT * FROM rec WHERE id > ? ORDER BY id", (last_id,))
    if not rows:
        tg("no new recorder rows")
        return
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["id", "t0", "asset", "trig", "tf", "o", "up", "data"])
    for r in rows:
        w.writerow([r["id"], r["t0"], r["asset"], r["trig"], r["tf"], r["o"], r["up"], zlib.decompress(r["data"]).decode()])
    tg_doc("combo_rec.csv.gz", gzip.compress(buf.getvalue().encode()), f"{len(rows)} recorder rows")
    oc = dbq("SELECT * FROM outcomes")
    b2 = io.StringIO()
    w2 = csv.writer(b2)
    w2.writerow(["asset", "tf", "o", "outcome"])
    w2.writerows([[x["asset"], x["tf"], x["o"], x["outcome"]] for x in oc])
    tg_doc("combo_outcomes.csv.gz", gzip.compress(b2.getvalue().encode()), f"{len(oc)} market results")
    kv_set("rec_last_id", rows[-1]["id"])


def old_early2_export():
    """one-off: send the early2 data the OLD 50secmaker code saved in its database (still on this volume) before the switch"""
    path = os.environ.get("OLD_DB", os.path.join(os.path.dirname(DB_PATH) or ".", "paper_favorite_dip.db"))
    if not os.path.exists(path):
        tg(f"old database not found at {path}")
        return
    try:
        c = sqlite3.connect(f"file:{path}?mode=ro", uri=True, timeout=30)
        c.row_factory = sqlite3.Row
        days = [r[0] for r in c.execute("SELECT DISTINCT CAST(t0/86400 AS INTEGER) FROM e2_early ORDER BY 1").fetchall()]
        tg(f"old early2: {len(days)} days found, sending one file per day…")
        for d in days:
            rows = c.execute("SELECT t0, asset, feed, level, data FROM e2_early WHERE t0 >= ? AND t0 < ? ORDER BY t0", (d * 86400, (d + 1) * 86400)).fetchall()
            buf = io.StringIO()
            w = csv.writer(buf)
            w.writerow(["t0", "asset", "feed", "level", "data"])
            w.writerows([tuple(r) for r in rows])
            day = datetime.fromtimestamp(d * 86400, timezone.utc).strftime("%Y-%m-%d")
            tg_doc(f"early2_old_{day}.csv.gz", gzip.compress(buf.getvalue().encode()), f"{len(rows)} rows, {day} (UTC)")
        mk = c.execute("SELECT asset, tf, open_ts, open, outcome FROM e2_mkts WHERE outcome IS NOT NULL ORDER BY open_ts").fetchall()
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(["asset", "tf", "open_ts", "open", "outcome"])
        w.writerows([tuple(r) for r in mk])
        tg_doc("early2_mkts_old.csv.gz", gzip.compress(buf.getvalue().encode()), f"{len(mk)} market results")
        c.close()
    except Exception as e:
        tg(f"old early2 export failed: {str(e)[:200]}")


cl_gaps = {a: deque(maxlen=20000) for a in ASSETS}   # (when, seconds since the previous new Chainlink price)
FT = deque(maxlen=20000)       # (t0, ft10): BTC 3bp jumps and how far BTC kept going their way 10s later (bp)


def ft_watch(t0, feed, bps):
    """Nov 14: the follow-through meter. P5's edge is BTC jumps carrying on; Nov 12-14 they carried on far less than in research."""
    try:
        sg = 1 if bps > 0 else -1
        p0 = last("BTC", "vis", t0)
        time.sleep(max(0.0, t0 + 10 - time.time()))
        p1 = last("BTC", "vis")
        if p0 and p1:
            ft = round((p1 / p0 - 1) * 1e4 * sg, 3)
            FT.append((t0, ft))
            dbx("INSERT INTO ftrack (t0, feed, bps, ft10) VALUES (?,?,?,?)", (t0, feed, bps, ft))
    except Exception as e:
        _err("ft_watch", e)


def ft_stats(window, t=None):
    """share of BTC 3bp jumps still going their way 10s later, avg bp, count, over the last `window` seconds (results known by t)"""
    t = t or time.time()
    xs = [f for (ts, f) in list(FT) if t - window <= ts <= t - 10]
    if len(xs) < 5:
        return None, None, len(xs)
    return round(sum(1 for f in xs if f > 0) / len(xs), 3), round(sum(xs) / len(xs), 2), len(xs)


def ft_line():
    def one(lbl, w):
        c, m, n = ft_stats(w)
        return f"{lbl} {c * 100:.0f}% ({m:+.2f}bp, {n})" if c is not None else f"{lbl} -"
    c3 = ft_stats(3 * 3600)[0]
    mood = "" if c3 is None else (" 🟢 normal" if c3 >= 0.62 else " 🟡 weak" if c3 >= 0.58 else " 🔴 very weak")
    return "BTC jump follow-through (still going 10s later; research days 60-74%): " + " · ".join(
        [one("1h", 3600), one("3h", 3 * 3600), one("24h", 86400)]) + mood


def ft_load():
    try:
        for r in dbq("SELECT t0, ft10 FROM ftrack WHERE t0 > ? ORDER BY t0", (time.time() - 86400,)):
            FT.append((r["t0"], r["ft10"]))
    except Exception as e:
        _err("ft_load", e)


def on_move(a, trig, feed, bps, t0):
    try:
        if a == "BTC" and trig == 3:
            threading.Thread(target=ft_watch, args=(t0, feed, bps), daemon=True).start()
        threading.Thread(target=dbx, args=("INSERT INTO moves (t0, asset, trig, feed, bps, fut_lag) VALUES (?,?,?,?,?,?)",
                                          (t0, a, trig, feed, bps, st.get("fut_lag"))), daemon=True).start()
        threading.Thread(target=rec_capture, args=(a, trig, feed, bps, t0), daemon=True).start()
        sg = 1 if bps > 0 else -1
        up = sg > 0
        with lock:                                                             # every jump is remembered (the "clean move" rules count them)
            JH.setdefault((a, trig), deque(maxlen=5000)).append((t0, sg))
        lc_ = live_codes()
        rules = sorted((r for r in RULES if r.asset == a and r.trig == trig and not r.follow),
                       key=lambda r: r.code not in lc_)                      # live rules are looked at first, paper rules after
        for fr in [r for r in RULES if r.follow == a and r.trig == trig]:      # follow rules: this coin jumped -> trade another coin's market
            with lock:
                fm = [(k, dict(v)) for k, v in markets.items() if k[0] == fr.asset and k[1] == fr.tf and k[2] <= t0 < k[2] + k[1] * 60]
            for (fa, ftf, fo), m in fm:                                        # own thread: never slows the BTC rules
                threading.Thread(target=lambda fa=fa, ftf=ftf, fo=fo, m=m, fr=fr: eval_market(
                    fa, ftf, fo, m, up, t0, feed, bps, fairs(fa, ftf, fo, t0), 0.0, 0.0, [fr], 0.0), daemon=True).start()
        tfs = {r.tf for r in rules}
        with lock:
            mk = [(k, dict(v)) for k, v in markets.items() if k[0] == a and k[1] in tfs and k[2] <= t0 < k[2] + k[1] * 60]
        if not mk:
            return
        m10, m2 = lead_mean(a, t0, -10, sg), lead_mean(a, t0, -2, sg)
        for (a_, tf, o), m in mk:
            fu = fairs(a, tf, o, t0)                                     # fair from prices at the jump
            if (a, tf, trig) in LOOK_KEYS:                                # remember both sides' asks + fairs for the dip / flat / persist rules
                ua, da = asks_of(m["up"], 1), asks_of(m["dn"], 1)
                with lock:
                    LOOKS.setdefault((a, tf, o), deque(maxlen=4000)).append(
                        (t0, sg, ua[0][0] if ua else None, da[0][0] if da else None, fu))
            if trig == 2:                                                 # ETH + 1h/4h rules: the recorder they were found on read the ask
                late_r = [r for r in rules if not r.early]
                now_r = [r for r in rules if r.early]                   # rules found on real-time data read the ask at the jump
                if late_r:
                    threading.Thread(target=eval_market, args=(a, tf, o, m, up, t0, feed, bps, fu, m10, m2, late_r, ENTRY_DELAY),
                                     daemon=True).start()                 # ~0.3s after the jump (after Polymarket repriced), so we do too
                if now_r:
                    eval_market(a, tf, o, m, up, t0, feed, bps, fu, m10, m2, now_r, 0.0)
            else:
                eval_market(a, tf, o, m, up, t0, feed, bps, fu, m10, m2, rules, 0.0)
    except Exception as e:
        _err("on_move", e)


def decide(r, c):
    key = (r.code, c["a"], c["tf"], c["o"])
    try:
        t0 = c["t0"]
        threading.Thread(target=bump, args=(r.code, "pre"), daemon=True).start()
        a25 = None
        if (r.R and not c.get("late")) or (r.lc and not c.get("late")):
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
        if r.lc_min is not None:                     # other exchanges must follow the jump by >= lc_min bp within 0.5s (no R check)
            time.sleep(max(0.0, t0 + 0.55 - time.time()))
            p05 = lead_mean(c["a"], t0, 0.5, c.get("sg") or (1 if c["up"] else -1))
            if p05 is None or p05 < r.lc_min:
                bump(r.code, "lc_fail")
                return
        if r.bc is not None:                         # Binance must keep going our way by >= bc bp within 0.5s of the jump
            time.sleep(max(0.0, t0 + 0.5 - time.time()))
            sg_ = 1 if c["up"] else -1
            p0, p1 = last(c["a"], "vis", t0), last(c["a"], "vis", t0 + 0.5)
            cont = (p1 / p0 - 1) * 1e4 * sg_ if (p0 and p1) else None
            if cont is None or cont < r.bc:
                bump(r.code, "bc_fail")
                return
            la = asks_of(c["tok"], 1)
            if not la:
                return
            a25 = la[0][0]                           # the price we actually face now; the limit is set from it
        with dlock:
            if key in done and r.conf != "first":
                return
            done.add(key)
        base = a25 if a25 is not None else c["a0"]
        cap = min(99.0, base + r.cap)
        live = live_on() and r.code in live_codes() and not in_quiet_hours(r, t0)   # quiet hours: 5m rules trade on paper only
        stk = stake()
        if live and in_quiet_hours(r, t0, "half_hours"):  # half hours: 5m rules trade at half stake (below Polymarket's $1 minimum -> paper)
            stk = round(stk / 2, 2)
            if stk < MIN_ORDER - 1e-9:
                live, stk = False, stake()
        head = f"{r.name} {c['side']} {c['tf'] if c['tf'] < 60 else c['tf'] // 60}{'m' if c['tf'] < 60 else 'h'} · ask {c['a0']:g}¢" + \
               (f" fair {c['fair']:.0f}¢" if c["fair"] is not None else "")
        why, ok, resp, note, tim = None, False, {}, "", {}
        snap = {}
        threading.Thread(target=twin_snap, args=(c, snap), daemon=True).start()   # paper price is photographed on time, order or no order
        if live:                                   # order first, bookkeeping after (every millisecond counts)
            why = risk_check(r, c, stk)
            if not why:
                try:
                    ok, resp, note = buy(c["tok"], stk, cap, tim)
                except Exception as e:
                    ok, resp, note = False, {}, f"error: {str(e)[:150]}"
        lag = ((tim.get("resp") or time.time()) - t0) if tim else None
        if not live:                               # paper bookkeeping waits until 0.4s after the jump, out of the way of any live order
            time.sleep(max(0.0, t0 + 0.4 - time.time()))   # (the paper price is read later anyway: 1s after the jump, 0.5s on 15m)
        fc, fm, fn = ft_stats(3 * 3600, t0) if c["a"] == "BTC" else (None, None, None)
        volr, j1h, ar1h = road(c["a"], t0)
        rid = dbx("INSERT INTO trades (code, rule, asset, tf, o, side, mode, status, t0, feed, bps, ask0, a25, fair, gap, left_s, m10, m2, p05, cap, stake, token, cond, "
                  "t_sent, t_resp, lag, bk_age, a0_ts, t_build, ft_c, ft_m, ft_n, volr, j1h, ar1h, fk, n_same, n_opp, t_hdr, pm_lag) "
                  "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                  (r.code, r.name, c["a"], c["tf"], c["o"], c["side"], "LIVE" if live else "PAPER", "SIGNAL", t0, c["feed"], c["bps"], c["a0"], a25,
                   c["fair"], c["gap"], c["left"], c["m10"], c["m2"], p05, cap, stk if live else 1.0, c["tok"], c["cond"],
                   tim.get("sent"), tim.get("resp"), lag, c["bk_age"], c["a0_ts"], tim.get("build"), fc, fm, fn, volr, j1h, ar1h,
                   c.get("fk"), c.get("n_same"), c.get("n_opp"), tim.get("hdr"), c.get("pm_lag")))
        st["signals"] += 1
        threading.Thread(target=paper_twin, args=(r, c, rid, cap, live, key, snap), daemon=True).start()
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
        if st["balance"] is not None:
            st["balance"] -= cost                   # keep our cash figure current between the 60s balance checks
        RISK["open"] += 1                           # counts at once, before risk_worker's next recount
        bump(r.code, "filled")
        dbx("UPDATE trades SET status='HOLDING', cost=?, shares=?, buy_px=? WHERE id=?", (cost, shares, bpx, rid))
        if not quiet():
            tg(f"🎯 {head} · bought ${cost:.2f} at {bpx:.0f}¢ · {lag:.2f}s after the jump")
    except Exception as e:
        _err("decide_" + r.code, e)


TWIN_OFF = 2.0        # Nov 19: the paper twin prices off the book 2s after the jump (was 1s; 0.5s on 15m) ...
TWIN_ADD = 1.0        # ... plus 1c, and the price is rounded UP to the next whole cent. Fees are rounded up to the next cent as before.
                      # Why: on 1,200+ real fills (Nov 12-19) the 1s book was too kind (P5O paper +$24.51, real +$11.78; LC5 paper +$3.40,
                      # real -$9.22). The 2s book matched real money (P5O +$12.74, LC5 -$8.80); +1c keeps paper a little BELOW real.


def cautious(cost, sh):
    """the cautious paper fill: same dollars, price 1c worse and rounded up to the next cent -> (cost, shares, price)"""
    if cost <= 0 or sh <= 0:
        return 0.0, 0.0, None
    px = min(99.0, float(math.ceil(cost / sh * 100 + TWIN_ADD - 1e-9)))
    return cost, cost / (px / 100), px


def twin_snap(c, snap):
    """photographs our side's asks 1s (0.5s on 15m) and 2s after the jump. Started BEFORE any live order goes out, so a slow
    order no longer makes the paper price late (it did before Nov 19: the twin of a live trade waited for the order's answer)."""
    try:
        for k, off in (("old", 0.5 if c["tf"] == 15 else 1.0), ("new", TWIN_OFF)):
            time.sleep(max(0.0, c["t0"] + off - time.time()))
            snap[k] = asks_of(c["tok"], 25)
    except Exception as e:
        _err("twin_snap", e)
    snap["done"] = True


def paper_twin(r, c, rid, cap, live, key, snap):
    """what the paper rule pays for $1 and $100, up to the limit. p_ columns = the cautious price (2s book, +1c, rounded up);
    q_ columns = the old 1s-book price, kept only so the two can be compared in /export."""
    try:
        t_end = time.time() + 6
        while not snap.get("done") and time.time() < t_end:
            time.sleep(0.02)
        old, new = snap.get("old") or [], snap.get("new") or []
        q1, qs1 = walk(old, 1.0, cap)
        q100, qs100 = walk(old, 100.0, cap)
        c1, s1, px1 = cautious(*walk(new, 1.0, cap))
        c100, s100, _ = cautious(*walk(new, 100.0, cap))
        dbx("UPDATE trades SET p_cost1=?, p_sh1=?, p_cost100=?, p_sh100=?, p_px=?, q_cost1=?, q_sh1=?, q_cost100=?, q_sh100=?, q_px=? WHERE id=?",
            (c1, s1, c100, s100, px1, q1, qs1, q100, qs100, (q1 / qs1 * 100) if qs1 > 0 else None, rid))
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
    if time.time() - RISK["ts"] < 5:                 # fresh numbers from risk_worker (no database on the trading path)
        today, n_open = RISK["today"], RISK["open"]
    else:                                            # fallback if the worker stalled
        t_day = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
        today = dbq("SELECT COALESCE(SUM(pnl),0) s FROM trades WHERE mode='LIVE' AND status='SETTLED' AND t0 >= ?", (t_day,))[0]["s"]
        n_open = dbq("SELECT COUNT(*) n FROM trades WHERE mode='LIVE' AND status='HOLDING' AND t0 >= ?", (t_day - 86400,))[0]["n"]
    if today <= -DAILY_LOSS:
        kv_set("paused", f"paused: daily loss limit ${DAILY_LOSS:g} reached (today {money(today)})")
        tg(f"🛑 Live trading PAUSED: today's live result is {money(today)} (limit ${DAILY_LOSS:g}). It stays paused until midnight, or /resume.")
        return paused()
    if n_open >= MAX_OPEN:
        return f"{n_open} trades already open (max {MAX_OPEN})"
    cap_r = rule_loss_cap()                          # Nov 16: one rule on a bad day can't use up the whole daily stop
    if cap_r > 0 and RISK["by_code"].get(r.code, 0.0) <= -cap_r:
        return f"paused for today: {r.code} is down {money(RISK['by_code'][r.code])} (rule limit ${cap_r:g}); it keeps trading on paper"
    # (Nov 12: the "other side held" block was removed - each rule now trades exactly as it was tested; one trade per rule per market)
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
            asked = {}                                # Nov 19: one result lookup per market per pass (was one per trade row)
            for x in rows:
                mk_ = (x["asset"], x["tf"], x["o"])
                if mk_ not in asked:
                    if mk_ not in _outcomes:
                        time.sleep(0.2)                # only real web lookups are spaced out
                    asked[mk_] = outcome(*mk_)
                oc = asked[mk_]
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
                q1 = ((x["q_sh1"] if won else 0) - x["q_cost1"] - fee_of(x["q_sh1"], x["q_cost1"])) if (x.get("q_cost1") or 0) > 0 else None
                q100 = ((x["q_sh100"] if won else 0) - x["q_cost100"] - fee_of(x["q_sh100"], x["q_cost100"])) if (x.get("q_cost100") or 0) > 0 else None
                dbx("UPDATE trades SET outcome=?, won=?, pnl=?, p_pnl1=?, p_pnl100=?, q_pnl1=?, q_pnl100=?, status=?, settled_ts=? WHERE id=?",
                    (oc, won, pnl, p1, p100, q1, q100, status, now, x["id"]))
                if x["mode"] == "LIVE" and pnl is not None and not quiet():
                    t_day = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
                    td = dbq("SELECT COALESCE(SUM(pnl),0) s, COUNT(*) n FROM trades WHERE mode='LIVE' AND status='SETTLED' AND t0 >= ?", (t_day,))[0]
                    tg(f"{'✅' if won else '❌'} {x['rule']} {x['side']} at {x['buy_px']:.0f}¢ · {money(pnl)} · today {money(td['s'])} ({td['n']} trades)")
            with dlock:
                for k in [k for k in list(done) if k[3] + k[2] * 60 < now - 600]:
                    done.discard(k)
            with lock:                                # memory housekeeping: finished markets' looks, week-old results
                for k in [k for k in list(LOOKS) if k[2] + k[1] * 60 < now - 600]:
                    LOOKS.pop(k, None)
            for k in [k for k in list(_outcomes) if k[2] + k[1] * 60 < now - 7 * 86400]:
                _outcomes.pop(k, None)
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
    lines = [f"📊 {label} — live = real money, twin = cautious paper ($1 / $100 a trade: book 2s after the jump, +1¢, rounded up)"]
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
        pre, rf, cs = s.get("pre", 0), s.get("r_fail", 0), s.get("cl_stale", 0)
        lines.append(f"{r.code}: filled {len(fil)}/{len(att)}" + (f" · median {lags[len(lags) // 2]:.2f}s jump→answer" if lags else "")
                     + (f" · paid {sum(slip) / len(slip):+.1f}¢ vs paper" if slip else "") + (f" · {100 * sum(part) / len(part):.0f}% of stake filled" if part else "")
                     + (f" · R-check fails {rf}/{pre}" if pre and (r.R or r.lc) else (f" · {pre} signals" if pre else ""))
                     + (f" · {cs} skipped (Chainlink old)" if cs else ""))
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
             + (f" · clock vs Binance {st['fut_lag']:+.3f}s" if st.get("fut_lag") is not None else "")
             + f" · book reconnects {st.get('pm_drops', 0)}"]
    for a in ASSETS:
        lines.append(f"{a}: binance {age(a, 'vis')}/{age(a, 'spot')}/{age(a, 'fut')} · others " + " ".join(f"{v} {age(a, v)}" for v in LEAD_V)
                     + f" · chainlink {age(a, 'cl')} · twap feed {'%.0fs' % (now - tw_feed[a][-1][0]) if tw_feed[a] else 'none'} · deribit iv {ivs[a].get('iv')}"
                     + (f" (5m/15m: {iv50.get('iv')})" if a == "BTC" else ""))
    lines.append(ft_line())
    rd = []
    for a in ASSETS:
        v, j, ar = road(a, now)
        rd.append(f"{a} real vs Deribit volatility {v:.2f}x" + (f" · 1h move {ar:.0f}bp" if ar is not None else "") if v else f"{a} vol -")
    j1 = sum(1 for (ts, f) in list(FT) if now - 3600 <= ts <= now)
    lines.append("road: " + " | ".join(rd) + f" | BTC 3bp jumps last hour {j1}  (above 1.0x = wilder than the Deribit fair assumes)")
    qh, hh, cr = quiet_hours(), quiet_hours("half_hours"), rule_loss_cap()
    lines.append("quiet hours (5m rules paper-only): " + (f"{qh[0]}:00-{qh[1]}:00 Toronto" if qh else "off") +
                 " · half hours (5m rules half stake): " + (f"{hh[0]}:00-{hh[1]}:00" if hh else "off") +
                 " · per-rule daily loss limit: " + (f"${cr:g}" if cr > 0 else "off"))
    for a in ASSETS:
        g = [x for t, x in list(cl_gaps[a]) if t > now - 3600]
        if g:
            lines.append(f"{a} chainlink last 1h: {len(g)} prices · longest gap {max(g):.1f}s · gaps over 3s: {sum(1 for x in g if x > 3)}")
    sk = {x["code"]: x["n"] for x in dbq("SELECT code, SUM(n) n FROM stats WHERE day=? AND k='cl_stale' GROUP BY code", (day_str(),))}
    if sk:
        lines.append("skipped today (Chainlink >20s old): " + ", ".join(f"{k} {v}" for k, v in sorted(sk.items())))
    if st["err"]:
        lines.append("last errors: " + " | ".join(f"{k}: {v}" for k, v in list(st["err"].items())[-5:]))
    return "\n".join(lines)


def rules_text():
    lc = live_codes()
    return "📋 rules (code · name · LIVE/paper)\n" + "\n".join(f"{r.code:<4} {r.name} · {'LIVE' if r.code in lc else 'paper'} · limit +{r.cap:g}¢" for r in RULES) + \
        "\n\nAdaptive fair in use now (P5A, E5A):\n" + ad_text() + "\n\n/live CODE on|off to switch one rule"


def trades_text(n=12):
    rows = dbq("SELECT * FROM trades WHERE mode='LIVE' ORDER BY id DESC LIMIT ?", (n,))
    if not rows:
        return "no live trades yet"
    out = []
    for x in rows:
        t = datetime.fromtimestamp(x["t0"], TZ).strftime("%m-%d %H:%M:%S")
        res = money(x["pnl"]) if x["pnl"] is not None else x["status"].lower()
        out.append(f"{t} {x['code']} {x['side']} ask {(x['ask0'] or 0):g}¢" + (f" paid {x['buy_px']:.0f}¢" if x["buy_px"] else "") +
                   (f" {x['lag']:.2f}s" if x["lag"] else "") + f" · {res}" + (f" · {x['note'][:60]}" if x["note"] and x["status"] in ("BLOCKED", "MISSED") else ""))
    return "\n".join(out)


def export():
    rows = dbq("SELECT * FROM trades ORDER BY id")
    mv = dbq("SELECT * FROM moves WHERE t0 > ? ORDER BY t0", (time.time() - 3 * 86400,))
    ftr = dbq("SELECT * FROM ftrack ORDER BY t0")
    for name, rs in (("combo_trades.csv.gz", rows), ("combo_copiers.csv.gz", dbq("SELECT * FROM copiers ORDER BY id")), ("combo_moves.csv.gz", mv),
                     ("combo_follow.csv.gz", ftr)):
        if not rs:
            continue
        buf = io.StringIO()
        w = csv.DictWriter(buf, fieldnames=list(rs[0].keys()))
        w.writeheader()
        w.writerows(rs)
        tg_doc(name, gzip.compress(buf.getvalue().encode()), f"{len(rs)} rows")


HELP = """COMBO bot commands
/status — live on/off, cash, open trades, feeds, follow-through meter, road conditions
/quiethours 18-21 — 5-minute rules trade on paper only in those Toronto hours (off to cancel)
/halfhours 0-3 — 5-minute rules trade at half stake in those Toronto hours (off to cancel)
/rulestop 8 — a live rule down $8 on the day stops until midnight (off to cancel)
/rules — every rule, live or paper
/live on | /live off — all live rules on/off (/stop = off)
/live CODE on|off — one rule (e.g. /live ELS5 on)
/stake 1 — dollars per live trade (max MAX_STAKE)
/resume — clear a pause (loss limit / errors)
/pnl [today|yday|week|all] — live + paper twin per rule
/trades [n] — last live trades
/edge [today|yday|week] — fill rate, speed, price vs paper
/copiers — wallets buying right after us
/export — CSV of every trade + copier log + jumps + follow-through log
/recexport — research recorder, new rows since last time (/recexport all = everything)
/summary — the table for the last 30 min now · /summary 20 — every 20 min
/quiet off|on — per-trade messages on/off (off by default)
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
    elif cmd == "/summary":
        if args and args[0].isdigit() and 5 <= int(args[0]) <= 240:
            kv_set("summary_min", args[0])
            tg(f"summary every {args[0]} min")
        else:
            n = int(float(kv_get("summary_min", "30")))
            now = time.time()
            t_b = now
            tg(summary_text(now - n * 60, now, n), pre=True)
    elif cmd == "/quiethours":
        if not args:
            qh = quiet_hours()
            tg("quiet hours: " + (f"{qh[0]}:00-{qh[1]}:00 Toronto (5-minute rules trade on paper only)" if qh else "off") +
               "\nset with /quiethours 18-21 · turn off with /quiethours off")
        elif args[0].lower() == "off":
            kv_set("quiet_hours", "")
            tg("quiet hours OFF: the 5-minute rules trade live all day")
        else:
            kv_set("quiet_hours", args[0])
            qh = quiet_hours()
            if qh:
                tg(f"quiet hours ON: live 5-minute rules (P5, LC5 ...) do not trade real money {qh[0]}:00-{qh[1]}:00 Toronto time. "
                   f"They keep trading on paper then, so we can check the pause is still right.")
            else:
                kv_set("quiet_hours", "")
                tg("couldn't read that. Use start-end hours, like /quiethours 18-21")
    elif cmd == "/halfhours":
        if not args:
            hh = quiet_hours("half_hours")
            tg("half hours: " + (f"{hh[0]}:00-{hh[1]}:00 Toronto (5-minute rules trade at half stake)" if hh else "off") +
               "\nset with /halfhours 0-3 · turn off with /halfhours off")
        elif args[0].lower() == "off":
            kv_set("half_hours", "")
            tg("half hours OFF")
        else:
            kv_set("half_hours", args[0])
            hh = quiet_hours("half_hours")
            if hh:
                tg(f"half hours ON: live 5-minute rules trade at half stake {hh[0]}:00-{hh[1]}:00 Toronto time "
                   f"(now ${stake() / 2:g} a trade" + (", which is under Polymarket's $1 minimum, so those trades go to paper until the stake is $2+)" if stake() / 2 < MIN_ORDER else ")"))
            else:
                kv_set("half_hours", "")
                tg("couldn't read that. Use start-end hours, like /halfhours 0-3")
    elif cmd == "/rulestop":
        if not args:
            cr = rule_loss_cap()
            tg("per-rule daily loss limit: " + (f"${cr:g}" if cr > 0 else "off") + "\nset with /rulestop 8 · turn off with /rulestop off")
        elif args[0].lower() == "off":
            kv_set("rule_loss", "0")
            tg("per-rule daily loss limit OFF (the overall daily stop still applies)")
        else:
            try:
                v = float(args[0].replace("$", ""))
                kv_set("rule_loss", str(v))
                tg(f"per-rule daily loss limit ${v:g}: a live rule that is down ${v:g} on the day stops trading real money until midnight "
                   f"(it keeps trading on paper). The overall daily stop ${DAILY_LOSS:g} still applies.")
            except ValueError:
                tg("use a number, like /rulestop 8")
    elif cmd == "/quiet":
        on_ = not args or args[0].lower() == "on"
        kv_set("quiet", "1" if on_ else "0")
        tg("quiet: no per-trade messages (pauses, errors and the midnight summary still come)" if on_ else "per-trade messages ON")
    elif cmd == "/copiers":
        tg(copiers_text())
    elif cmd == "/oldearly2":
        threading.Thread(target=old_early2_export, daemon=True).start()
    elif cmd == "/recexport":
        rec_export(bool(args and args[0].lower() == "all"))
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
        except requests.exceptions.ReadTimeout:
            pass
        except Exception as e:
            _err("telegram", e)
            time.sleep(5)


def _f(x):
    return f"{x:+.2f}"


def summary_text(t_a, t_b, minutes):
    lc = live_codes()
    a_s = datetime.fromtimestamp(t_a, TZ).strftime("%-I:%M")
    b_s = datetime.fromtimestamp(t_b, TZ).strftime("%-I:%M%p").lower()
    head = f"📊 {a_s}–{b_s} · LIVE {'ON' if live_on() else 'OFF'} · ${stake():g}/trade" + (f"\n⛔ {paused()}" if paused() else "")
    st_rows = dbq("SELECT * FROM trades WHERE settled_ts >= ? AND settled_ts < ? AND mode IN ('LIVE','PAPER')", (t_a, t_b))
    act = dbq("SELECT * FROM trades WHERE t0 >= ? AND t0 < ? AND mode='LIVE'", (t_a, t_b))
    seen_tw = {(x["code"], x["asset"], x["tf"], x["o"]) for x in dbq(
        "SELECT code, asset, tf, o FROM trades WHERE p_cost1 > 0 AND settled_ts < ? AND settled_ts > ?", (t_a, t_a - 2 * 86400))}
    L = [head, "", f"{'Rule':<5}{'Trades':>7}{'Won':>4}{'P&L':>7}{'Paper':>7}"]
    T = [0, 0, 0.0, 0.0]
    pap = []
    for r in RULES:
        rr = [x for x in st_rows if x["code"] == r.code]
        live = [x for x in rr if x["mode"] == "LIVE" and (x["cost"] or 0) > 0 and x["pnl"] is not None]
        tw, k_ = [], set()
        for x in sorted(rr, key=lambda x: x["t0"]):
            k = (x["code"], x["asset"], x["tf"], x["o"])
            if (x["p_cost1"] or 0) > 0 and x["p_pnl1"] is not None and k not in k_ and k not in seen_tw:
                k_.add(k)
                tw.append(x)
        pp = sum(x["p_pnl1"] for x in tw)
        if r.code in lc:
            n, w, pl = len(live), sum(x["won"] for x in live), sum(x["pnl"] for x in live)
            L.append(f"{r.code:<5}{n:>7}{(w if n else '-'):>4}{(_f(pl) if n else '-'):>7}{(_f(pp) if tw else '-'):>7}")
            T[0] += n; T[1] += w; T[2] += pl; T[3] += pp
        else:
            pap.append(f"{r.code} {len(tw)}/{sum(x['won'] for x in tw)} {_f(pp)}" if tw else f"{r.code} 0")
    L.append(f"{'Total':<5}{T[0]:>7}{T[1]:>4}{_f(T[2]):>7}{_f(T[3]):>7}")
    d0 = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    td = dbq("SELECT COUNT(*) n, COALESCE(SUM(won),0) w, COALESCE(SUM(pnl),0) s FROM trades WHERE mode='LIVE' AND status='SETTLED' AND t0 >= ?", (d0,))[0]
    op = dbq("SELECT COUNT(*) n, COALESCE(SUM(cost),0) c FROM trades WHERE mode='LIVE' AND status='HOLDING'")[0]
    miss = [x for x in act if x["status"] == "MISSED"]
    blk = [x for x in act if x["status"] == "BLOCKED"]
    why = {}
    for x in blk:
        k = (x["note"] or "").split(" ")[0:2]
        k = "cash floor" if "floor" in (x["note"] or "") else ("other side held" if "other side" in (x["note"] or "") else
                                                                ("max open" if "already open" in (x["note"] or "") else (x["note"] or "")[:20]))
        why[k] = why.get(k, 0) + 1
    L += ["", f"Today: {td['n']} trades · {(100 * td['w'] / td['n']) if td['n'] else 0:.0f}% won · {money(td['s'])}",
          f"Cash {'$%.2f' % st['balance'] if st['balance'] is not None else '?'} · open {op['n']} (${op['c']:.2f})",
          f"Not filled {len(miss)} · skipped {len(blk)}" + (" (" + ", ".join(f"{k} {v}" for k, v in why.items()) + ")" if why else ""),
          "", "Paper rules (at $1):"]
    for i in range(0, len(pap), 3):
        L.append(" · ".join(pap[i:i + 3]))
    return "\n".join(L)


def summary_worker():
    """a table every N minutes (default 30, /summary 20 to change), at :00 and :30"""
    last = None
    while True:
        try:
            n = int(float(kv_get("summary_min", "30")))
            slot = int(time.time() // (n * 60))
            if last is None:
                last = slot
            elif slot != last:
                last = slot
                t_b = slot * n * 60
                t_a = t_b - n * 60
                busy = dbq("SELECT 1 FROM trades WHERE (settled_ts >= ? AND settled_ts < ?) OR (t0 >= ? AND t0 < ? AND mode='LIVE') LIMIT 1", (t_a, t_b, t_a, t_b))
                if live_on() or busy:
                    tg(summary_text(t_a, t_b, n), pre=True)
        except Exception as e:
            _err("summary", e)
        time.sleep(15)


def daily_worker():
    """just after midnight Toronto: yesterday's summary + edge tracker + copiers"""
    while True:
        try:
            d = day_str()
            if kv_get("summary_day") is None:
                kv_set("summary_day", d)
            if kv_get("summary_day") != d and datetime.now(TZ).minute >= 1:
                kv_set("summary_day", d)
                if paused().startswith("paused: daily loss"):
                    kv_set("paused", "")
                    tg("🌅 new day: the daily loss pause is cleared, live trading continues.")
                tg(pnl_text(*_range("yday")))
                tg(edge_text(*_range("yday")))
                y0, y1 = _range("yday")[:2]
                xs = [f for (ts, f) in list(FT) if y0 <= ts < y1]
                if xs:
                    cy = sum(1 for f in xs if f > 0) / len(xs)
                    tg(f"📏 yesterday's BTC jump follow-through: {cy * 100:.0f}% of {len(xs)} jumps still going 10s later "
                       f"(avg {sum(xs) / len(xs):+.2f}bp) · research days were 60-74%, Nov 12-14 57-60% · "
                       + ("🟢 normal" if cy >= 0.62 else "🟡 weak" if cy >= 0.58 else "🔴 very weak"))
                if dbq("SELECT 1 FROM trades WHERE mode='LIVE' AND cost > 0 LIMIT 1"):
                    tg(copiers_text(1))
        except Exception as e:
            _err("daily", e)
        time.sleep(30)


def main():
    init_db()
    ft_load()
    threading.Thread(target=seed_px60, daemon=True).start()
    for x in dbq("SELECT code, asset, tf, o FROM trades WHERE t0 > ? AND (mode='SKIP' OR cost > 0 OR p_cost1 > 0 OR status IN ('SIGNAL','HOLDING'))",
                 (time.time() - 5 * 3600,)):
        done.add((x["code"], x["asset"], x["tf"], x["o"]))      # after a restart, never trade the same market twice
    for x in dbq("SELECT t0, asset, trig, bps FROM moves WHERE t0 > ? ORDER BY t0", (time.time() - 4.5 * 3600,)):
        JH.setdefault((x["asset"], x["trig"]), deque(maxlen=5000)).append((x["t0"], 1 if x["bps"] > 0 else -1))   # jump memory survives a restart
    if LIVE_START and kv_get("live_on") is None:
        kv_set("live_on", "1")
    workers = [market_worker, open_worker, pm_worker, chainlink_worker, twap_feed_worker, deribit_worker, settler, balance_worker,
               copier_worker, telegram_worker, daily_worker, warm_worker, summary_worker, rec_outcome_worker,
               kv_worker, risk_worker, keepalive_worker, ad_worker]
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
