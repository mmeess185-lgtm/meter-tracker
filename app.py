"""Wareef meter tracker: electricity and water meters and their monthly bills.

Environment variables (set in Render):
  MONGO_URI     database link (same one the other trackers use)
  APP_PASSWORD  optional: if set, people must type it to open the site
  PORT          set by Render automatically
"""
import csv
import hashlib
import hmac
import html
import io
import json
import math
import os
import re
import threading
import time
import traceback
import uuid
from datetime import datetime, timedelta, timezone
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

from pymongo import ASCENDING, DESCENDING, MongoClient
from pymongo.errors import DuplicateKeyError

MONGO_URI = os.environ.get("MONGO_URI", "")
APP_PASSWORD = os.environ.get("APP_PASSWORD", "")
DB_NAME = "employee_tracker"
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
LOGO_NAMES = {"wareef", "se", "nwc"}
PAGE_SIZE = 50
MAX_BODY = 64 * 1024
SESSION_SECONDS = 12 * 3600
COOKIE_NAME = "meters_session"
TYPES = {"electricity", "water"}
RIYADH = timezone(timedelta(hours=3))

client = MongoClient(MONGO_URI, serverSelectionTimeoutMS=8000) if MONGO_URI else None
db = client[DB_NAME] if client is not None else None
meters = db["meters"] if db is not None else None
bills = db["meter_bills"] if db is not None else None


def ensure_indexes():
    if db is None:
        return
    try:
        meters.create_index([("type", ASCENDING), ("meter_no", ASCENDING)], unique=True)
        bills.create_index([("meter_id", ASCENDING), ("period", ASCENDING)], unique=True)
        bills.create_index([("type", ASCENDING), ("period", ASCENDING)])
    except Exception:
        traceback.print_exc()


def today():
    return datetime.now(RIYADH).strftime("%Y-%m-%d")


def current_period():
    return today()[:7]


# ---------- login ----------

_fail_lock = threading.Lock()
_fails = []
FAIL_WINDOW = 300
FAIL_LIMIT = 20


def login_locked():
    now = time.time()
    with _fail_lock:
        _fails[:] = [t for t in _fails if now - t < FAIL_WINDOW]
        return len(_fails) >= FAIL_LIMIT


def note_failed_login():
    with _fail_lock:
        _fails.append(time.time())


def _session_key():
    return hashlib.sha256(b"meter-tracker-session:" + APP_PASSWORD.encode("utf-8")).digest()


def make_token():
    expires = str(int(time.time()) + SESSION_SECONDS)
    sig = hmac.new(_session_key(), expires.encode(), hashlib.sha256).hexdigest()
    return expires + "." + sig


def token_valid(token):
    if not APP_PASSWORD or not token or "." not in token:
        return False
    expires, sig = token.split(".", 1)
    if not expires.isdigit() or int(expires) < time.time():
        return False
    good = hmac.new(_session_key(), expires.encode(), hashlib.sha256).hexdigest()
    return hmac.compare_digest(sig, good)


# ---------- validation ----------

class BadInput(Exception):
    """The message is a key the page translates."""


def clean(value, limit=200):
    if value is None:
        return ""
    return str(value).strip()[:limit]


def check_type(value):
    if value not in TYPES:
        raise BadInput("bad_type")
    return value


def check_period(value):
    if not re.fullmatch(r"\d{4}-(0[1-9]|1[0-2])", value or ""):
        raise BadInput("bad_period")
    return value


def check_date(value, required=False):
    value = clean(value, 10)
    if not value:
        if required:
            raise BadInput("need_due_date")
        return ""
    try:
        datetime.strptime(value, "%Y-%m-%d")
    except ValueError:
        raise BadInput("bad_date")
    return value


def check_amount(value):
    try:
        amount = round(float(value), 2)
    except (TypeError, ValueError):
        raise BadInput("bad_amount")
    if not math.isfinite(amount) or amount < 0 or amount > 100000000:
        raise BadInput("bad_amount")
    return amount


def meter_fields(body):
    account = clean(body.get("account_no"), 60)
    number = clean(body.get("meter_no"), 60)
    if not number:
        raise BadInput("need_meter_no")
    if not account:
        raise BadInput("need_account_no")
    return {
        "account_no": account,
        "meter_no": number,
        "building": clean(body.get("building"), 120),
        "unit": clean(body.get("unit"), 60),
        "holder": clean(body.get("holder"), 120),
        "note": clean(body.get("note"), 500),
    }


def bill_status(bill):
    if not bill:
        return "none"
    if bill.get("paid"):
        return "paid"
    if bill.get("due_date") and bill["due_date"] < today():
        return "overdue"
    return "unpaid"


# ---------- data ----------

def joined_rows(meter_type, period, search, building):
    found = list(meters.find({"type": meter_type}, {"_id": 0}))
    found.sort(key=lambda m: (m.get("building", ""), m.get("meter_no", "")))
    by_meter = {
        b["meter_id"]: b
        for b in bills.find({"type": meter_type, "period": period}, {"_id": 0})
    }
    needle = search.lower()
    rows = []
    for meter in found:
        if building and meter.get("building") != building:
            continue
        if needle:
            past = [e.get("old", "") for e in meter.get("number_log", [])]
            text = " ".join(
                [str(meter.get(k, "")) for k in ("account_no", "meter_no", "building", "unit", "holder")] + past
            ).lower()
            if needle not in text:
                continue
        bill = by_meter.get(meter["id"])
        transfer = meter.get("transfer") or {}
        gone = transfer.get("state") == "done" and not bill and period >= transfer.get("done_date", "")[:7]
        rows.append({"meter": meter, "bill": bill, "status": bill_status(bill), "gone": gone})
    return rows, sorted({m["building"] for m in found if m.get("building")})


def list_view(query):
    meter_type = check_type(query.get("type", ""))
    period = check_period(query.get("month", ""))
    status = query.get("status", "")
    rows, buildings = joined_rows(
        meter_type, period, clean(query.get("q"), 80), clean(query.get("building"), 120)
    )
    counts = {"none": 0, "unpaid": 0, "overdue": 0, "paid": 0}
    total = paid = 0.0
    live = [r for r in rows if not r["gone"]]
    state = lambda r: (r["meter"].get("transfer") or {}).get("state")
    need_transfer = [r for r in live if state(r) == "pending"]
    transferred = [r for r in rows if state(r) == "done"]
    for row in live:
        counts[row["status"]] += 1
        if row["bill"]:
            total += row["bill"].get("amount", 0)
            if row["bill"].get("paid"):
                paid += row["bill"].get("amount", 0)
    if status == "transfer":
        shown = need_transfer
    elif status == "transferred":
        shown = transferred
    elif status in counts:
        shown = [r for r in live if r["status"] == status]
    else:
        shown = live
    pages = max(1, math.ceil(len(shown) / PAGE_SIZE))
    try:
        page = min(max(1, int(query.get("page", 1))), pages)
    except ValueError:
        page = 1
    start = (page - 1) * PAGE_SIZE
    return {
        "rows": shown[start:start + PAGE_SIZE],
        "page": page,
        "pages": pages,
        "shown": len(shown),
        "buildings": buildings,
        "summary": {
            "meters": len(live),
            "transfer": len(need_transfer),
            "transferred": len(transferred),
            "counts": counts,
            "total": round(total, 2),
            "paid": round(paid, 2),
        },
    }


def save_bill(body):
    meter = meters.find_one({"id": clean(body.get("meter_id"), 40)}, {"_id": 0})
    if not meter:
        raise BadInput("meter_gone")
    is_paid = bool(body.get("paid"))
    fields = {
        "type": meter["type"],
        "amount": check_amount(body.get("amount")),
        "due_date": check_date(body.get("due_date"), required=True),
        "bill_no": clean(body.get("bill_no"), 60),
        "paid": is_paid,
        "paid_date": (check_date(body.get("paid_date")) or today()) if is_paid else "",
        "note": clean(body.get("note"), 500),
        "updated": datetime.now(timezone.utc).isoformat(),
    }
    period = check_period(clean(body.get("period"), 7))
    bills.update_one(
        {"meter_id": meter["id"], "period": period},
        {
            "$set": fields,
            "$setOnInsert": {"meter_no": meter["meter_no"], "account_no": meter["account_no"]},
        },
        upsert=True,
    )


def update_meter(meter_id, body):
    """Saves meter details and logs any change to its account or meter number."""
    current = meters.find_one({"id": meter_id}, {"_id": 0})
    if not current:
        raise BadInput("meter_gone")
    fields = meter_fields(body)
    changed_on = check_date(body.get("change_date")) or today()
    logged = datetime.now(timezone.utc).isoformat()
    entries = [
        {"id": uuid.uuid4().hex, "field": key, "old": current.get(key, ""),
         "new": fields[key], "date": changed_on, "logged": logged}
        for key in ("account_no", "meter_no", "holder")
        if current.get(key, "") != fields[key]
    ]
    update = {"$set": fields}
    if entries:
        update["$push"] = {"number_log": {"$each": entries}}
    meters.update_one({"id": meter_id}, update)


def meter_history(meter_id):
    meter = meters.find_one({"id": meter_id}, {"_id": 0})
    if not meter:
        raise BadInput("meter_gone")
    found = list(bills.find({"meter_id": meter_id}, {"_id": 0}).sort("period", DESCENDING).limit(60))
    for bill in found:
        bill["status"] = bill_status(bill)
    log = sorted(meter.get("number_log", []), key=lambda e: (e["date"], e["logged"]), reverse=True)
    unpaid = [b for b in found if not b.get("paid")]
    return {
        "meter": meter,
        "bills": found,
        "log": log,
        "unpaid_count": len(unpaid),
        "unpaid_total": round(sum(b.get("amount", 0) for b in unpaid), 2),
    }


def change_transfer(meter_id, body):
    meter = meters.find_one({"id": meter_id}, {"_id": 0})
    if not meter:
        raise BadInput("meter_gone")
    action = body.get("action")
    current = meter.get("transfer") or {}
    if action == "flag":
        meters.update_one({"id": meter_id}, {"$set": {"transfer": {
            "state": "pending",
            "vacated_date": check_date(body.get("date")) or today(),
            "new_owner": clean(body.get("new_owner"), 120),
            "note": clean(body.get("note"), 500),
        }}})
    elif action == "complete":
        owner = clean(body.get("new_owner"), 120)
        if not owner:
            raise BadInput("need_new_owner")
        done_date = check_date(body.get("date")) or today()
        update = {"$set": {
            "holder": owner,
            "transfer": {**current, "state": "done", "new_owner": owner,
                         "done_date": done_date, "note": clean(body.get("note"), 500)},
        }}
        if meter.get("holder", "") != owner:
            update["$push"] = {"number_log": {
                "id": uuid.uuid4().hex, "field": "holder", "old": meter.get("holder", ""),
                "new": owner, "date": done_date,
                "logged": datetime.now(timezone.utc).isoformat(),
            }}
        meters.update_one({"id": meter_id}, update)
    elif action == "cancel":
        meters.update_one({"id": meter_id}, {"$unset": {"transfer": ""}})
    else:
        raise BadInput("server")


def safe_cell(value):
    """Stops Excel from treating typed text as a formula."""
    text = "" if value is None else str(value)
    return "'" + text if text[:1] in ("=", "+", "-", "@") else text


STATUS_AR = {"none": "لا توجد فاتورة", "unpaid": "غير مسددة", "overdue": "متأخرة", "paid": "مسددة"}


def export_csv(query):
    meter_type = check_type(query.get("type", ""))
    period = check_period(query.get("month", ""))
    rows, _ = joined_rows(meter_type, period, "", "")
    out = io.StringIO()
    writer = csv.writer(out)
    writer.writerow([
        "رقم العداد", "رقم الحساب", "المبنى", "الوحدة", "صاحب الحساب", "الشهر",
        "المبلغ", "تاريخ الاستحقاق", "رقم الفاتورة", "الحالة", "تاريخ السداد", "ملاحظات", "نقل الحساب",
    ])
    for row in rows:
        if row["gone"]:
            continue
        transfer_state = (row["meter"].get("transfer") or {}).get("state")
        meter, bill = row["meter"], row["bill"] or {}
        writer.writerow([safe_cell(v) for v in (
            meter.get("meter_no"), meter.get("account_no"), meter.get("building"),
            meter.get("unit"), meter.get("holder"), period, bill.get("amount", ""),
            bill.get("due_date", ""), bill.get("bill_no", ""), STATUS_AR[row["status"]],
            bill.get("paid_date", ""), bill.get("note", ""),
            {"pending": "تم إخلاء الشقة - بانتظار نقل الحساب", "done": "تم نقل الحساب"}.get(transfer_state, ""),
        )])
    return ("﻿" + out.getvalue()).encode("utf-8")


# ---------- pages ----------

LOGIN_HTML = """<!doctype html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>وريف | العدادات</title>
<style>body{margin:0;min-height:100vh;display:grid;place-items:center;background:#eef5f4;color:#1f3a44;
font-family:"IBM Plex Sans Arabic",Tahoma,Arial,sans-serif}form{background:#fff;border:1px solid #d6dde1;
padding:32px;width:min(340px,88vw);display:grid;gap:14px;border-radius:4px}img{height:64px;justify-self:start}
h1{font-size:20px;margin:0}label{font-size:14px;color:#4d6a74}input{font:inherit;padding:11px;border:1px solid #aab7bf;
border-radius:3px;width:100%;box-sizing:border-box}button{font:inherit;font-weight:600;padding:11px;border:0;
border-radius:3px;background:#007f73;color:#fff;cursor:pointer}.e{color:#b3261e;font-size:14px;margin:0}</style></head>
<body><form method="post" action="/login"><img src="/logos/wareef.png" alt="" onerror="this.remove()">
<h1>عدادات الكهرباء والمياه</h1>__MSG__<label for="p">كلمة المرور | Password</label>
<input id="p" type="password" name="password" autocomplete="current-password" autofocus required>
<button>دخول | Sign in</button></form></body></html>"""

INDEX_HTML = r"""<!doctype html>
<html lang="ar" dir="rtl">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>وريف | العدادات</title>
<meta name="robots" content="noindex,nofollow">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=IBM+Plex+Sans+Arabic:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
:root{--bg:#eef5f4;--panel:#fff;--ink:#1f3a44;--muted:#4d6a74;--line:#d2e0df;--accent:#007f73;--slate:#577983;
--paid:#17724a;--unpaid:#7f5a00;--overdue:#b3261e;--none:#4d6a74}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.5 "IBM Plex Sans Arabic",Tahoma,Arial,sans-serif}
button,input,select,textarea{font:inherit;color:inherit}
button{cursor:pointer}
:focus-visible{outline:3px solid var(--accent);outline-offset:2px}
.wrap{max-width:1180px;margin:0 auto;padding:0 20px 56px}

.top{display:flex;align-items:center;justify-content:space-between;gap:20px;padding:12px 20px;background:var(--panel);border:1px solid var(--line);margin:8px 0 14px}
.brand{display:flex;align-items:center;justify-content:center;height:68px;min-width:130px}
.brand img{max-height:68px;max-width:170px;display:block}
.brand .ph{border:1px dashed #9aa9b2;color:var(--muted);font-size:12.5px;padding:8px 12px;text-align:center;max-width:170px;line-height:1.35}
.tools{display:flex;gap:6px;justify-content:flex-end;padding-top:10px}
.link{background:none;border:0;color:var(--muted);padding:2px 6px;font-size:13.5px;text-decoration:underline}

.tabs{display:flex;background:var(--ink);padding:5px;gap:5px;border-radius:5px}
.tab{flex:1;border:0;background:none;color:#d2e8e6;font-size:17px;font-weight:600;padding:9px 34px;border-radius:3px;white-space:nowrap}
.tab[aria-selected=true]{background:var(--accent);color:#fff}

.head{display:grid;grid-template-columns:auto 1fr;gap:28px;align-items:center;background:var(--panel);border:1px solid var(--line);border-top:4px solid var(--accent);padding:22px 24px;margin-bottom:14px}
.month{display:flex;align-items:center;gap:6px}
.month h1{font-size:25px;line-height:1.2;margin:0;min-width:172px;text-align:center;font-weight:700}
.step{width:38px;height:38px;border:1px solid var(--line);background:#fff;font-size:20px;line-height:1;border-radius:3px}
.reading{display:flex;flex-direction:column;align-items:flex-end;gap:7px}
[dir=ltr] .reading{align-items:flex-end}
.dial{display:flex;direction:ltr;gap:3px;align-items:stretch}
.dial span{display:grid;place-items:center;width:34px;height:50px;background:var(--ink);color:#fff;font-size:27px;font-weight:600;border-radius:2px;font-variant-numeric:tabular-nums;font-family:Tahoma,Arial,sans-serif}
.dial span.frac{background:var(--accent)}
.dial span.dim{color:#7f9aa3}
.dial i{width:5px}
.sub{color:var(--muted);font-size:14px}
.sub b{color:var(--ink);font-weight:600}

.chips{display:flex;flex-wrap:wrap;gap:8px;margin-bottom:14px}
.chip{border:1px solid var(--line);background:var(--panel);padding:7px 14px;border-radius:3px;display:flex;gap:9px;align-items:baseline}
.chip b{font-size:17px;font-variant-numeric:tabular-nums}
.chip[aria-pressed=true]{background:var(--ink);border-color:var(--ink);color:#fff}
.chip.overdue:not([aria-pressed=true]) b{color:var(--overdue)}

.bar{display:flex;flex-wrap:wrap;gap:8px;margin-bottom:14px}
.bar input,.bar select{padding:9px 11px;border:1px solid #aab7bf;border-radius:3px;background:#fff}
.bar input{flex:1 1 220px}
.bar select{flex:0 1 200px}
.btn{padding:9px 16px;border:1px solid #aab7bf;background:#fff;border-radius:3px;font-weight:500}
.btn.main{background:var(--accent);border-color:var(--accent);color:#fff;font-weight:600}
.btn.danger{color:var(--overdue);border-color:var(--overdue)}

.table{background:var(--panel);border:1px solid var(--line);overflow-x:auto}
table{width:100%;border-collapse:collapse}
th{font-size:13px;font-weight:600;color:var(--muted);text-align:start;padding:10px 14px;border-bottom:2px solid var(--line);white-space:nowrap}
td{padding:11px 14px;border-bottom:1px solid var(--line);vertical-align:middle}
tr:last-child td{border-bottom:0}
td.num{font-variant-numeric:tabular-nums;white-space:nowrap}
td small{display:block;color:var(--muted);font-size:13px}
.m{background:none;border:0;padding:0;font-weight:600;color:var(--accent);text-decoration:underline;font-variant-numeric:tabular-nums}
.st{font-size:13.5px;font-weight:600;white-space:nowrap}
.st.paid{color:var(--paid)}.st.unpaid{color:var(--unpaid)}.st.overdue{color:var(--overdue)}.st.none{color:var(--none)}
.acts{display:flex;gap:6px;justify-content:flex-end;flex-wrap:nowrap}
.acts .btn{padding:5px 11px;font-size:13.5px;white-space:nowrap}
.empty{padding:46px 24px;text-align:center;color:var(--muted)}
.empty b{display:block;color:var(--ink);font-size:17px;margin-bottom:4px}
.pager{display:flex;gap:10px;justify-content:center;align-items:center;padding:14px;color:var(--muted)}

dialog{border:0;padding:0;border-radius:5px;width:min(600px,94vw);color:var(--ink);border-top:4px solid var(--accent)}
dialog::backdrop{background:rgba(23,38,47,.55)}
.dlg{padding:22px 24px}
.dlg h2{margin:0;font-size:19px}
.dlg .ctx{color:var(--muted);font-size:14px;margin:2px 0 16px}
.grid{display:grid;grid-template-columns:1fr 1fr;gap:12px}
.f{display:grid;gap:4px}.f.full{grid-column:1/-1}
.f label{font-size:13.5px;color:var(--muted)}
.f input,.f textarea{padding:9px 11px;border:1px solid #aab7bf;border-radius:3px;width:100%;background:#fff}
.check{display:flex;align-items:center;gap:8px;grid-column:1/-1;font-weight:500}
.check input{width:18px;height:18px}
.err{color:var(--overdue);font-size:14px;margin:12px 0 0;min-height:0}
.foot{display:flex;gap:8px;margin-top:18px;flex-wrap:wrap}
.foot .sp{flex:1}
.hist{width:100%;max-height:230px;overflow:auto}
.dlg h3{font-size:15px;margin:14px 0 6px}
.arrow{color:var(--muted);padding:0 5px}
.flag td{background:#fdf3dc;color:#5f4400;font-size:14px;padding:7px 14px;border-bottom:1px solid var(--line)}
.flag .row{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap}
.notice{background:#fdf3dc;color:#5f4400;padding:11px 14px;margin-bottom:6px;font-size:14.5px}
.notice.done{background:#e1f2ee;color:#0c5a50}
.notice b{font-weight:600}
.notice .foot{margin-top:9px}
.xs{background:none;border:0;color:var(--overdue);text-decoration:underline;font-size:13px;padding:0}
.toast{position:fixed;inset-inline-start:20px;bottom:20px;background:var(--ink);color:#fff;padding:10px 16px;border-radius:3px;z-index:9}
[hidden]{display:none!important}

@media(max-width:760px){
 .top{flex-wrap:wrap;justify-content:space-between}
 .tabs{order:3;width:100%}
 .tab{padding:9px 8px}
 .top{padding:12px}
 .brand{height:50px;min-width:90px}.brand img{max-height:50px;max-width:130px}
 .head{grid-template-columns:1fr;gap:14px;padding:16px}
 .month{justify-content:space-between}
 .reading{align-items:center!important}
 .dial span{width:27px;height:42px;font-size:22px}
 .table{border:0;background:none;overflow:visible}
 table,tbody,tr,td{display:block;width:100%}
 thead{display:none}
 tr{background:var(--panel);border:1px solid var(--line);margin-bottom:9px;padding:6px 0}
 td{border:0;padding:5px 14px;display:flex;justify-content:space-between;gap:14px}
 td::before{content:attr(data-l);color:var(--muted);font-size:13px}
 td small{display:inline;margin-inline:8px}
 .acts{justify-content:flex-start;width:100%}
 .acts::before{display:none}
 td.a::before{display:none}
 .flag td::before{display:none}
 .flag{padding:0;border-top:0;margin-top:-10px}
 .grid{grid-template-columns:1fr}
}
@media(prefers-reduced-motion:no-preference){
 .tab{transition:background .15s}
}
</style>
</head>
<body data-type="electricity">
<div class="wrap">
  <div class="tools">
    <button class="link" id="lang"></button>
    <form method="post" action="/logout" style="margin:0"><button class="link" id="logout"></button></form>
  </div>
  <header class="top">
    <div class="brand" id="brandWareef"></div>
    <div class="tabs" role="tablist">
      <button class="tab" role="tab" data-tab="electricity"></button>
      <button class="tab" role="tab" data-tab="water"></button>
    </div>
    <div class="brand" id="brandProvider"></div>
  </header>

  <section class="head">
    <div class="month">
      <button class="step" id="prev"></button>
      <h1 id="monthName" aria-live="polite"></h1>
      <button class="step" id="next"></button>
    </div>
    <div class="reading">
      <div class="dial" id="dial" role="img"></div>
      <div class="sub" id="sub"></div>
    </div>
  </section>

  <div class="chips" id="chips"></div>

  <div class="bar">
    <input id="q" type="search">
    <select id="building"></select>
    <button class="btn" id="export"></button>
    <button class="btn main" id="addMeter"></button>
  </div>

  <div class="table"><div id="list"></div></div>
  <div class="pager" id="pager"></div>
</div>

<dialog id="meterDlg"><form class="dlg" method="dialog" id="meterForm" novalidate>
  <h2 id="meterTitle"></h2><p class="ctx" id="meterCtx"></p>
  <div class="grid">
    <div class="f"><label for="mNo" data-t="meter_no"></label><input id="mNo" required maxlength="60" dir="ltr"></div>
    <div class="f"><label for="mAcc" data-t="account_no"></label><input id="mAcc" required maxlength="60" dir="ltr"></div>
    <div class="f full" id="changeWrap" hidden><label for="mChange" data-t="change_date"></label><input id="mChange" type="date"></div>
    <div class="f"><label for="mBld" data-t="building"></label><input id="mBld" maxlength="120" list="bldList"><datalist id="bldList"></datalist></div>
    <div class="f"><label for="mUnit" data-t="unit"></label><input id="mUnit" maxlength="60"></div>
    <div class="f full"><label for="mHolder" data-t="holder"></label><input id="mHolder" maxlength="120"></div>
    <div class="f full"><label for="mNote" data-t="note"></label><textarea id="mNote" rows="2" maxlength="500"></textarea></div>
  </div>
  <p class="err" id="meterErr"></p>
  <div class="foot">
    <button class="btn main" id="meterSave" type="submit" data-t="save_meter"></button>
    <button class="btn" type="button" data-close="meterDlg" data-t="cancel"></button>
    <span class="sp"></span>
    <button class="btn danger" type="button" id="meterDel" data-t="delete_meter"></button>
  </div>
</form></dialog>

<dialog id="billDlg"><form class="dlg" method="dialog" id="billForm" novalidate>
  <h2 id="billTitle"></h2><p class="ctx" id="billCtx"></p>
  <div class="grid">
    <div class="f"><label for="bAmt" data-t="amount"></label><input id="bAmt" inputmode="decimal" dir="ltr"></div>
    <div class="f"><label for="bDue" data-t="due_date"></label><input id="bDue" type="date"></div>
    <div class="f full"><label for="bNo" data-t="bill_no"></label><input id="bNo" maxlength="60" dir="ltr"></div>
    <label class="check"><input id="bPaid" type="checkbox"><span data-t="is_paid"></span></label>
    <div class="f" id="paidDateWrap"><label for="bPaidDate" data-t="paid_date"></label><input id="bPaidDate" type="date"></div>
    <div class="f full"><label for="bNote" data-t="note"></label><textarea id="bNote" rows="2" maxlength="500"></textarea></div>
  </div>
  <p class="err" id="billErr"></p>
  <div class="foot">
    <button class="btn main" type="submit" id="billSaveNext" data-t="save_next"></button>
    <button class="btn" type="button" id="billSave" data-t="save_bill"></button>
    <button class="btn" type="button" data-close="billDlg" data-t="cancel"></button>
    <span class="sp"></span>
    <button class="btn danger" type="button" id="billDel" data-t="delete_bill"></button>
  </div>
</form></dialog>

<dialog id="histDlg"><div class="dlg">
  <h2 id="histTitle"></h2><p class="ctx" id="histCtx"></p>
  <div id="transferBox"></div>
  <h3 data-t="numbers_log"></h3>
  <div class="hist" id="histLog"></div>
  <h3 data-t="bills_log"></h3>
  <div class="hist" id="histBody"></div>
  <div class="foot">
    <button class="btn main" id="histEdit" data-t="edit_meter"></button>
    <button class="btn" id="histVacate" data-t="vacated_btn"></button>
    <button class="btn" data-close="histDlg" data-t="close"></button>
  </div>
</div></dialog>

<dialog id="trDlg"><form class="dlg" method="dialog" id="trForm" novalidate>
  <h2 id="trTitle"></h2><p class="ctx" id="trCtx"></p>
  <div class="grid">
    <div class="f"><label for="trDate" id="trDateL"></label><input id="trDate" type="date"></div>
    <div class="f"><label for="trOwner" data-t="new_owner"></label><input id="trOwner" maxlength="120"></div>
    <div class="f full"><label for="trNote" data-t="note"></label><textarea id="trNote" rows="2" maxlength="500"></textarea></div>
  </div>
  <p class="err" id="trErr"></p>
  <div class="foot">
    <button class="btn main" type="submit" id="trSave"></button>
    <button class="btn" type="button" data-close="trDlg" data-t="cancel"></button>
  </div>
</form></dialog>

<div class="toast" id="toast" role="status" hidden></div>

<script>
var T={ar:{
title:"العدادات",electricity:"الكهرباء",water:"المياه",langBtn:"English",logout:"تسجيل الخروج",
provider_electricity:"السعودية للطاقة",provider_water:"شركة المياه الوطنية",wareef:"وريف",logo_pending:"شعار",
sar:"ر.س",month_total:"إجمالي فواتير الشهر",paid_of:"المسدد",of:"من",meter_word:"عداد",
all:"الكل",none:"لا توجد فاتورة",unpaid:"غير مسددة",overdue:"متأخرة",paid:"مسددة",
search:"ابحث برقم العداد أو الحساب (الحالي أو القديم) أو المبنى",all_buildings:"كل المباني",export_btn:"تصدير إلى Excel",add_meter:"إضافة عداد",
meter_no:"رقم العداد",account_no:"رقم الحساب",building:"المبنى",unit:"الوحدة",holder:"صاحب الحساب",note:"ملاحظات",
amount:"المبلغ (ر.س)",due_date:"تاريخ الاستحقاق",bill_no:"رقم الفاتورة",is_paid:"تم السداد",paid_date:"تاريخ السداد",
status:"الحالة",actions:"",enter_bill:"إدخال الفاتورة",edit_bill:"تعديل",mark_paid:"تسديد",
save_meter:"حفظ العداد",save_bill:"حفظ",save_next:"حفظ والتالي",cancel:"إلغاء",close:"إغلاق",delete_meter:"حذف العداد",delete_bill:"حذف الفاتورة",edit_meter:"تعديل بيانات العداد",
new_meter:"إضافة عداد",edit_meter_t:"تعديل بيانات العداد",bill_for:"فاتورة شهر",history:"سجل العداد",no_history:"لم تُسجل أي فاتورة لهذا الحساب بعد.",numbers_log:"سجل التغييرات",bills_log:"الفواتير",no_changes:"لم يتغير رقم العداد أو الحساب أو صاحب الحساب حتى الآن.",change_date:"تاريخ التغيير",account_short:"حساب",remove:"حذف",log_date:"التاريخ",change_col:"التغيير",log_removed:"تم حذف السجل",confirm_log:"هل تريد حذف هذا السجل؟ استخدم هذا فقط لو كان التغيير خطأً مطبعياً.",transfer_chip:"تحتاج نقل حساب",transferred_chip:"تم نقلها",vacated_btn:"تم إخلاء الشقة",vacated_msg:"تم إخلاء الشقة. يرجى تصفية الفاتورة ونقل الحساب باسم المالك الجديد.",vacated_on:"تاريخ الإخلاء",new_owner:"المالك الجديد",transfer_done_btn:"تم نقل الحساب",transfer_cancel_btn:"إلغاء التنبيه",transfer_undo_btn:"إرجاع الحساب",flag_title:"تسجيل إخلاء الشقة",complete_title:"تأكيد نقل الحساب",save_flag:"حفظ التنبيه",save_complete:"تأكيد النقل",done_on:"تاريخ النقل",done_msg:"تم نقل الحساب إلى",on_date:"بتاريخ",unpaid_warn:"فواتير غير مسددة",no_unpaid:"لا توجد فواتير غير مسددة.",confirm_unpaid:"هذا الحساب عليه فواتير غير مسددة. هل تريد تأكيد النقل رغم ذلك؟",confirm_cancel:"هل تريد إلغاء تنبيه نقل الحساب؟",confirm_undo:"هل تريد إرجاع هذا الحساب إلى القائمة؟ لن يتغير اسم صاحب الحساب تلقائياً.",flag_saved:"تم حفظ التنبيه",transfer_saved:"تم نقل الحساب",transfer_cancelled:"تم الإلغاء",need_new_owner:"أدخل اسم المالك الجديد.",need_account_no:"أدخل رقم الحساب.",dup_meter:"رقم العداد هذا مسجل مسبقاً.",
empty_title:"لا توجد عدادات بعد",empty_body:"أضف أول عداد للبدء.",nomatch_title:"لا توجد نتائج",nomatch_body:"غيّر البحث أو الفلتر لعرض عدادات أخرى.",
page:"صفحة",prev:"السابق",next:"التالي",meter_saved:"تم حفظ العداد",bill_saved:"تم حفظ الفاتورة",bill_paid:"تم تسديد الفاتورة",meter_deleted:"تم حذف العداد",bill_deleted:"تم حذف الفاتورة",
confirm_meter:"سيتم حذف هذا العداد وكل فواتيره نهائياً. هل تريد المتابعة؟",confirm_bill:"هل تريد حذف فاتورة هذا الشهر؟",
need_meter_no:"أدخل رقم العداد.",need_due_date:"أدخل تاريخ الاستحقاق.",bad_amount:"أدخل المبلغ بالأرقام.",bad_date:"التاريخ غير صحيح.",bad_period:"الشهر غير صحيح.",bad_type:"نوع العداد غير صحيح.",meter_gone:"هذا العداد لم يعد موجوداً.",network:"تعذر الاتصال. تحقق من الإنترنت وحاول مرة أخرى.",server:"تعذر تنفيذ العملية. حاول مرة أخرى."
},en:{
title:"Meters",electricity:"Electricity",water:"Water",langBtn:"العربية",logout:"Sign out",
provider_electricity:"SE",provider_water:"National Water Company",wareef:"Wareef",logo_pending:"Logo",
sar:"SAR",month_total:"Bills this month",paid_of:"Paid",of:"of",meter_word:"meters",
all:"All",none:"No bill yet",unpaid:"Unpaid",overdue:"Overdue",paid:"Paid",
search:"Search by meter, account (current or old) or building",all_buildings:"All buildings",export_btn:"Export to Excel",add_meter:"Add meter",
meter_no:"Meter number",account_no:"Account number",building:"Building",unit:"Unit",holder:"Account holder",note:"Notes",
amount:"Amount (SAR)",due_date:"Due date",bill_no:"Bill number",is_paid:"Paid",paid_date:"Payment date",
status:"Status",actions:"",enter_bill:"Enter bill",edit_bill:"Edit",mark_paid:"Mark paid",
save_meter:"Save meter",save_bill:"Save",save_next:"Save and next",cancel:"Cancel",close:"Close",delete_meter:"Delete meter",delete_bill:"Delete bill",edit_meter:"Edit meter details",
new_meter:"Add meter",edit_meter_t:"Edit meter details",bill_for:"Bill for",history:"Meter record",no_history:"No bills recorded for this account yet.",numbers_log:"Change log",bills_log:"Bills",no_changes:"The meter number, account number and holder have not changed.",change_date:"Date of the change",account_short:"Account",remove:"Remove",log_date:"Date",change_col:"Change",log_removed:"Log entry removed",confirm_log:"Remove this log entry? Only do this if the change was a typing mistake.",transfer_chip:"Needs transfer",transferred_chip:"Transferred",vacated_btn:"Apartment vacated",vacated_msg:"Apartment vacated. Settle the bill and transfer the account to the new owner.",vacated_on:"Date vacated",new_owner:"New owner",transfer_done_btn:"Account transferred",transfer_cancel_btn:"Cancel alert",transfer_undo_btn:"Restore account",flag_title:"Record apartment vacated",complete_title:"Confirm account transfer",save_flag:"Save alert",save_complete:"Confirm transfer",done_on:"Transfer date",done_msg:"Account transferred to",on_date:"on",unpaid_warn:"unpaid bills",no_unpaid:"No unpaid bills.",confirm_unpaid:"This account has unpaid bills. Confirm the transfer anyway?",confirm_cancel:"Cancel the transfer alert?",confirm_undo:"Return this account to the list? The account holder name will not change automatically.",flag_saved:"Alert saved",transfer_saved:"Account transferred",transfer_cancelled:"Cancelled",need_new_owner:"Enter the name of the new owner.",need_account_no:"Enter the account number.",dup_meter:"This meter number is already registered.",
empty_title:"No meters yet",empty_body:"Add your first meter to get started.",nomatch_title:"No results",nomatch_body:"Change the search or filter to see other meters.",
page:"Page",prev:"Previous",next:"Next",meter_saved:"Meter saved",bill_saved:"Bill saved",bill_paid:"Bill marked paid",meter_deleted:"Meter deleted",bill_deleted:"Bill deleted",
confirm_meter:"This permanently deletes the meter and all its bills. Continue?",confirm_bill:"Delete this month's bill?",
need_meter_no:"Enter the meter number.",need_due_date:"Enter the due date.",bad_amount:"Enter the amount as a number.",bad_date:"That date is not valid.",bad_period:"That month is not valid.",bad_type:"That meter type is not valid.",meter_gone:"This meter no longer exists.",network:"Could not connect. Check the internet and try again.",server:"That did not go through. Try again."
}};
function store(k,v){try{if(v===undefined)return localStorage.getItem(k);localStorage.setItem(k,v)}catch(e){return null}}
var now=new Date(),S={lang:store("lang")==="en"?"en":"ar",type:store("type")==="water"?"water":"electricity",
month:now.getFullYear()+"-"+String(now.getMonth()+1).padStart(2,"0"),status:"",q:"",building:"",page:1,data:null};
function t(k){return T[S.lang][k]!==undefined?T[S.lang][k]:k}
function $(id){return document.getElementById(id)}
function esc(s){return String(s==null?"":s).replace(/[&<>"']/g,function(c){return{"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]})}
function money(n){return Number(n||0).toLocaleString("en-US",{minimumFractionDigits:2,maximumFractionDigits:2})}
function todayStr(){var d=new Date();return d.getFullYear()+"-"+String(d.getMonth()+1).padStart(2,"0")+"-"+String(d.getDate()).padStart(2,"0")}
function monthLabel(m){var p=m.split("-"),d=new Date(+p[0],+p[1]-1,1);
 return d.toLocaleDateString(S.lang==="ar"?"ar-u-ca-gregory-nu-latn":"en-GB",{month:"long",year:"numeric"})}
function shift(m,by){var p=m.split("-"),d=new Date(+p[0],+p[1]-1+by,1);return d.getFullYear()+"-"+String(d.getMonth()+1).padStart(2,"0")}
function show(id){var d=$(id);if(!d.open)d.showModal()}
function toast(k){var el=$("toast");el.textContent=t(k);el.hidden=false;clearTimeout(toast.h);toast.h=setTimeout(function(){el.hidden=true},2400)}

function api(method,url,body){
 return fetch(url,{method:method,headers:body?{"Content-Type":"application/json"}:{},body:body?JSON.stringify(body):undefined,credentials:"same-origin"})
 .then(function(r){if(r.status===401){location.reload();throw {key:"network"}}
  return r.json().catch(function(){return {}}).then(function(j){if(!r.ok)throw {key:j.error||"server"};return j})},
  function(e){if(e&&e.key)throw e;throw {key:"network"}})
}

function logo(el,file,label){
 el.innerHTML="";var img=new Image();img.alt=label;
 img.onerror=function(){el.innerHTML='<div class="ph">'+esc(t("logo_pending"))+"<br>"+esc(label)+"</div>"};
 img.src="/logos/"+file+".png";el.appendChild(img);
}
function chrome(){
 document.documentElement.lang=S.lang;document.documentElement.dir=S.lang==="ar"?"rtl":"ltr";
 document.body.dataset.type=S.type;document.title=t("wareef")+" | "+t(S.type);
 document.querySelectorAll("[data-t]").forEach(function(e){e.textContent=t(e.dataset.t)});
 document.querySelectorAll(".tab").forEach(function(b){b.textContent=t(b.dataset.tab);b.setAttribute("aria-selected",b.dataset.tab===S.type)});
 $("lang").textContent=t("langBtn");$("logout").textContent=t("logout");
 $("q").placeholder=t("search");$("q").setAttribute("aria-label",t("search"));$("export").textContent=t("export_btn");$("addMeter").textContent=t("add_meter");
 var rtl=S.lang==="ar";$("prev").textContent=rtl?"›":"‹";$("next").textContent=rtl?"‹":"›";
 $("prev").setAttribute("aria-label",t("prev"));$("next").setAttribute("aria-label",t("next"));
 logo($("brandWareef"),"wareef",t("wareef"));
 logo($("brandProvider"),S.type==="electricity"?"se":"nwc",t("provider_"+S.type));
 $("monthName").textContent=monthLabel(S.month);
}
function load(){
 var u="/api/list?"+new URLSearchParams({type:S.type,month:S.month,status:S.status,q:S.q,building:S.building,page:S.page});
 var ticket=load.n=(load.n||0)+1;
 return api("GET",u).then(function(d){if(ticket!==load.n)return;S.data=d;S.page=d.page;render()},function(e){toast(e.key)});
}
function dial(n){
 var parts=Number(n||0).toFixed(2).split("."),w=parts[0].padStart(7,"0"),h="",lead=true;
 for(var i=0;i<w.length;i++){if(w[i]!=="0"||i===w.length-1)lead=false;h+='<span class="'+(lead?"dim":"")+'">'+w[i]+"</span>"}
 return h+"<i></i><span class=frac>"+parts[1][0]+"</span><span class=frac>"+parts[1][1]+"</span>";
}
function render(){
 var d=S.data,s=d.summary;
 $("dial").innerHTML=dial(s.total);$("dial").setAttribute("aria-label",t("month_total")+": "+money(s.total)+" "+t("sar"));
 $("sub").innerHTML=esc(t("month_total"))+" "+esc(t("sar"))+" &nbsp;|&nbsp; "+esc(t("paid_of"))+" <b>"+money(s.paid)+"</b>";
 var c=[["",s.meters,"all"],["none",s.counts.none,"none"],["unpaid",s.counts.unpaid,"unpaid"],["overdue",s.counts.overdue,"overdue"],["paid",s.counts.paid,"paid"]];
 var c2=[["transfer",s.transfer,"transfer_chip"],["transferred",s.transferred,"transferred_chip"]];c=c.concat(c2.filter(function(x){return x[1]||S.status===x[0]}));
 $("chips").innerHTML=c.map(function(x){return '<button class="chip '+x[2]+'" data-status="'+x[0]+'" aria-pressed="'+(S.status===x[0])+'"><span>'+esc(t(x[2]))+"</span><b>"+x[1]+"</b></button>"}).join("");
 var opts='<option value="">'+esc(t("all_buildings"))+"</option>"+d.buildings.map(function(b){return '<option value="'+esc(b)+'"'+(b===S.building?" selected":"")+">"+esc(b)+"</option>"}).join("");
 $("building").innerHTML=opts;$("building").setAttribute("aria-label",t("building"));
 $("bldList").innerHTML=d.buildings.map(function(b){return '<option value="'+esc(b)+'">'}).join("");
 if(!d.rows.length){
  var virgin=!s.meters&&!S.q&&!S.building;
  $("list").innerHTML='<div class="empty"><b>'+esc(t(virgin?"empty_title":"nomatch_title"))+"</b>"+esc(t(virgin?"empty_body":"nomatch_body"))+"</div>";
 }else{
  var L=function(k){return ' data-l="'+esc(t(k))+'"'};
  $("list").innerHTML="<table><thead><tr><th>"+[t("meter_no"),t("building"),t("holder"),t("amount"),t("due_date"),t("status"),""].map(esc).join("</th><th>")+"</th></tr></thead><tbody>"+
  d.rows.map(function(r,i){var m=r.meter,b=r.bill||{},st=r.status,act,tr=m.transfer||{};
   if(r.gone)act="";
   else if(st==="none")act='<button class="btn main" data-bill="'+i+'">'+esc(t("enter_bill"))+"</button>";
   else{act=(st!=="paid"?'<button class="btn main" data-pay="'+i+'">'+esc(t("mark_paid"))+"</button>":"")+'<button class="btn" data-bill="'+i+'">'+esc(t("edit_bill"))+"</button>"}
   return "<tr><td"+L("meter_no")+'><span><button class="m" data-hist="'+i+'" dir="ltr">'+esc(m.meter_no)+"</button><small>"+esc(t("account_short"))+' <bdi dir="ltr">'+esc(m.account_no)+"</bdi></small></span></td>"+
   "<td"+L("building")+"><span>"+esc(m.building||"")+(m.unit?"<small>"+esc(m.unit)+"</small>":"")+"</span></td>"+
   "<td"+L("holder")+">"+esc(m.holder||"")+"</td>"+
   '<td class="num"'+L("amount")+">"+(r.bill?money(b.amount):"")+"</td>"+
   '<td class="num"'+L("due_date")+">"+esc(b.due_date||"")+"</td>"+
   "<td"+L("status")+'><span class="st '+st+'">'+esc(r.gone?t("transferred_chip"):t(st))+(b.paid_date?'<small class="num">'+esc(b.paid_date)+"</small>":"")+"</span></td>"+
   '<td class="a"><div class="acts">'+act+"</div></td></tr>"+
   (tr.state==="pending"?'<tr class="flag"><td colspan="7"><div class="row"><span>'+esc(t("vacated_msg"))+(tr.new_owner?" ("+esc(t("new_owner"))+": "+esc(tr.new_owner)+")":"")+'</span><button class="btn" data-hist="'+i+'">'+esc(t("transfer_done_btn"))+"</button></div></td></tr>":"")}).join("")+"</tbody></table>";
 }
 $("pager").innerHTML=d.pages>1?'<button class="btn" data-page="'+(d.page-1)+'"'+(d.page<=1?" disabled":"")+">"+esc(t("prev"))+"</button><span>"+esc(t("page"))+" "+d.page+" "+esc(t("of"))+" "+d.pages+'</span><button class="btn" data-page="'+(d.page+1)+'"'+(d.page>=d.pages?" disabled":"")+">"+esc(t("next"))+"</button>":"";
}
function refresh(){chrome();S.page=Math.max(1,S.page);return load()}

/* meter dialog */
var editing=null;
function openMeter(m){editing=m||null;$("meterErr").textContent="";
 $("meterTitle").textContent=t(m?"edit_meter_t":"new_meter");
 $("meterCtx").textContent=t(S.type);
 $("mNo").value=m?m.meter_no:"";$("mAcc").value=m?m.account_no||"":"";$("mChange").value=todayStr();$("changeWrap").hidden=true;$("mBld").value=m?m.building||"":(S.building||"");
 $("mUnit").value=m?m.unit||"":"";$("mHolder").value=m?m.holder||"":"";$("mNote").value=m?m.note||"":"";
 $("meterDel").hidden=!m;show("meterDlg");$("mNo").focus();
}
function numbersChanged(){return !!editing&&($("mNo").value.trim()!==editing.meter_no||$("mAcc").value.trim()!==editing.account_no||$("mHolder").value.trim()!==(editing.holder||""))}
["mNo","mAcc","mHolder"].forEach(function(id){$(id).addEventListener("input",function(){$("changeWrap").hidden=!numbersChanged()})});
$("meterForm").addEventListener("submit",function(e){e.preventDefault();
 var body={type:S.type,meter_no:$("mNo").value,account_no:$("mAcc").value,building:$("mBld").value,unit:$("mUnit").value,holder:$("mHolder").value,note:$("mNote").value,change_date:$("mChange").value};
 var keepOpen=!editing;
 (editing?api("PUT","/api/meters/"+editing.id,body):api("POST","/api/meters",body)).then(function(){
  toast("meter_saved");
  if(keepOpen){var bld=$("mBld").value,hld=$("mHolder").value;openMeter(null);$("mBld").value=bld;$("mHolder").value=hld}else $("meterDlg").close();
  load();
 },function(er){$("meterErr").textContent=t(er.key)});
});
$("meterDel").addEventListener("click",function(){if(!editing||!confirm(t("confirm_meter")))return;
 api("DELETE","/api/meters/"+editing.id).then(function(){$("meterDlg").close();toast("meter_deleted");load()},function(er){$("meterErr").textContent=t(er.key)})});

/* bill dialog */
var billIdx=-1,billMeter=null;
function openBill(i){var r=S.data.rows[i],b=r.bill||{};billIdx=i;billMeter=r.meter;$("billErr").textContent="";
 $("billTitle").textContent=t("bill_for")+" "+monthLabel(S.month);
 $("billCtx").textContent=t(S.type)+" | "+t("meter_no")+" "+r.meter.meter_no+" | "+t("account_short")+" "+r.meter.account_no+(r.meter.building?" | "+r.meter.building:"");
 $("bAmt").value=r.bill?b.amount:"";$("bDue").value=b.due_date||"";$("bNo").value=b.bill_no||"";
 $("bPaid").checked=!!b.paid;$("bPaidDate").value=b.paid_date||todayStr();$("bNote").value=b.note||"";
 $("paidDateWrap").hidden=!b.paid;$("billDel").hidden=!r.bill;show("billDlg");$("bAmt").focus();
}
$("bPaid").addEventListener("change",function(){$("paidDateWrap").hidden=!this.checked});
function billBody(){return{meter_id:billMeter.id,period:S.month,amount:$("bAmt").value.replace(/,/g,"").trim(),due_date:$("bDue").value,bill_no:$("bNo").value,paid:$("bPaid").checked,paid_date:$("bPaid").checked?$("bPaidDate").value:"",note:$("bNote").value}}
function saveBill(goNext){
 var from=billIdx,order=S.data.rows.slice(from+1).map(function(r){return r.status==="none"?r.meter.id:null}).filter(Boolean);
 api("PUT","/api/bills",billBody()).then(function(){toast("bill_saved");return load().then(function(){
  var idx=-1;if(goNext&&order.length){S.data.rows.some(function(r,i){if(r.meter.id===order[0]){idx=i;return true}})}
  if(idx>=0)openBill(idx);else $("billDlg").close();
 })},function(er){$("billErr").textContent=t(er.key)});
}
$("billForm").addEventListener("submit",function(e){e.preventDefault();saveBill(true)});
$("billSave").addEventListener("click",function(){saveBill(false)});
$("billDel").addEventListener("click",function(){if(!confirm(t("confirm_bill")))return;
 api("DELETE","/api/bills?"+new URLSearchParams({meter_id:billMeter.id,period:S.month})).then(function(){$("billDlg").close();toast("bill_deleted");load()},function(er){$("billErr").textContent=t(er.key)})});

/* history */
function showHist(m){
 billMeter=m;
 var cell=function(k,v,c){return '<td'+(c?' class="num"':'')+' data-l="'+esc(k)+'">'+v+"</td>"};
 return api("GET","/api/history?meter_id="+encodeURIComponent(m.id)).then(function(d){
  billMeter=d.meter;renderTransfer(d);
  $("histLog").innerHTML=!d.log.length?'<p class="sub">'+esc(t("no_changes"))+"</p>":
  "<table><thead><tr><th>"+esc(t("log_date"))+"</th><th>"+esc(t("change_col"))+"</th><th></th></tr></thead><tbody>"+d.log.map(function(e){
   return "<tr>"+cell(t("log_date"),esc(e.date),1)+cell(t("change_col"),"<span>"+esc(t(e.field))+': <bdi dir="ltr">'+esc(e.old)+'</bdi><span class="arrow">'+(S.lang==="ar"?"←":"→")+'</span><bdi dir="ltr">'+esc(e.new)+"</bdi></span>")+'<td class="a"><button class="xs" data-log="'+esc(e.id)+'">'+esc(t("remove"))+"</button></td></tr>"}).join("")+"</tbody></table>";
  $("histBody").innerHTML=!d.bills.length?'<p class="sub">'+esc(t("no_history"))+"</p>":
  "<table><thead><tr><th></th><th>"+esc(t("account_short"))+"</th><th>"+esc(t("amount"))+"</th><th>"+esc(t("due_date"))+"</th><th>"+esc(t("status"))+"</th></tr></thead><tbody>"+d.bills.map(function(b){
   return "<tr>"+cell("",esc(monthLabel(b.period)))+cell(t("account_short"),'<bdi dir="ltr">'+esc(b.account_no||"")+"</bdi>",1)+cell(t("amount"),money(b.amount),1)+cell(t("due_date"),esc(b.due_date||""),1)+cell(t("status"),'<span class="st '+b.status+'">'+esc(t(b.status))+"</span>")+"</tr>"}).join("")+"</tbody></table>";
 },function(e){$("histBody").textContent=t(e.key)});
}
var histData=null;
function renderTransfer(d){histData=d;var tr=d.meter.transfer||{},box=$("transferBox");
 $("histVacate").hidden=!!tr.state;
 if(tr.state==="pending"){
  box.innerHTML='<div class="notice"><b>'+esc(t("vacated_msg"))+"</b><br>"+esc(t("vacated_on"))+": "+esc(tr.vacated_date)+(tr.new_owner?" | "+esc(t("new_owner"))+": "+esc(tr.new_owner):"")+"<br>"+
  (d.unpaid_count?esc(t("unpaid_warn")+": "+d.unpaid_count+" | "+money(d.unpaid_total)+" "+t("sar")):esc(t("no_unpaid")))+
  '<div class="foot"><button class="btn main" id="trComplete">'+esc(t("transfer_done_btn"))+'</button><button class="btn" id="trCancel">'+esc(t("transfer_cancel_btn"))+"</button></div></div>";
 }else if(tr.state==="done"){
  box.innerHTML='<div class="notice done"><b>'+esc(t("done_msg"))+" "+esc(tr.new_owner)+"</b> "+esc(t("on_date"))+" "+esc(tr.done_date)+'<div class="foot"><button class="btn" id="trCancel">'+esc(t("transfer_undo_btn"))+"</button></div></div>";
 }else box.innerHTML="";
}
var trMode="";
function openTransfer(mode){var tr=billMeter.transfer||{};trMode=mode;$("trErr").textContent="";
 $("trTitle").textContent=t(mode==="flag"?"flag_title":"complete_title");
 $("trCtx").textContent=t("meter_no")+" "+billMeter.meter_no+(billMeter.building?" | "+billMeter.building:"")+(billMeter.unit?" | "+billMeter.unit:"");
 $("trDateL").textContent=t(mode==="flag"?"vacated_on":"done_on");$("trSave").textContent=t(mode==="flag"?"save_flag":"save_complete");
 $("trDate").value=todayStr();$("trOwner").value=tr.new_owner||"";$("trNote").value=tr.note||"";show("trDlg");$("trOwner").focus();
}
function afterTransfer(key){toast(key);load();return showHist(billMeter)}
$("trForm").addEventListener("submit",function(e){e.preventDefault();
 if(trMode==="complete"&&histData&&histData.unpaid_count&&!confirm(t("confirm_unpaid")))return;
 api("POST","/api/meters/"+billMeter.id+"/transfer",{action:trMode,date:$("trDate").value,new_owner:$("trOwner").value,note:$("trNote").value}).then(function(){$("trDlg").close();return afterTransfer(trMode==="flag"?"flag_saved":"transfer_saved")},function(er){$("trErr").textContent=t(er.key)});
});
$("histVacate").addEventListener("click",function(){openTransfer("flag")});
$("transferBox").addEventListener("click",function(e){
 if(e.target.id==="trComplete")openTransfer("complete");
 else if(e.target.id==="trCancel"){var done=(billMeter.transfer||{}).state==="done";if(confirm(t(done?"confirm_undo":"confirm_cancel")))api("POST","/api/meters/"+billMeter.id+"/transfer",{action:"cancel"}).then(function(){return afterTransfer("transfer_cancelled")},function(er){toast(er.key)})}
});
function openHist(i){var m=S.data.rows[i].meter;
 $("histTitle").textContent=t("history")+" "+m.meter_no;
 $("histCtx").textContent=[t(S.type),t("account_short")+" "+m.account_no,m.building,m.unit,m.holder].filter(Boolean).join(" | ");
 $("histLog").textContent="";$("histBody").textContent="";$("transferBox").innerHTML="";show("histDlg");showHist(m);
}
$("histEdit").addEventListener("click",function(){$("histDlg").close();openMeter(billMeter)});

/* events */
document.addEventListener("click",function(e){
 var c=e.target.closest("[data-close]");if(c){$(c.dataset.close).close();return}
 var el=e.target.closest("[data-tab],[data-status],[data-bill],[data-pay],[data-hist],[data-page],[data-log]");if(!el)return;
 var x=el.dataset;
 if(x.log){if(confirm(t("confirm_log")))api("DELETE","/api/meters/"+billMeter.id+"/log/"+x.log).then(function(){toast("log_removed");showHist(billMeter);load()},function(er){toast(er.key)})}
 else if(x.tab){if(S.type!==x.tab){S.type=x.tab;store("type",S.type);S.status="";S.q="";S.building="";S.page=1;$("q").value="";refresh()}}
 else if(x.status!==undefined){S.status=x.status;S.page=1;load()}
 else if(x.bill!==undefined)openBill(+x.bill);
 else if(x.hist!==undefined)openHist(+x.hist);
 else if(x.page){S.page=+x.page;load();scrollTo(0,0)}
 else if(x.pay!==undefined){var r=S.data.rows[+x.pay],b=r.bill;
  api("PUT","/api/bills",{meter_id:r.meter.id,period:S.month,amount:b.amount,due_date:b.due_date,bill_no:b.bill_no,paid:true,paid_date:todayStr(),note:b.note}).then(function(){toast("bill_paid");load()},function(er){toast(er.key)})}
});
$("prev").addEventListener("click",function(){S.month=shift(S.month,-1);S.page=1;$("monthName").textContent=monthLabel(S.month);load()});
$("next").addEventListener("click",function(){S.month=shift(S.month,1);S.page=1;$("monthName").textContent=monthLabel(S.month);load()});
$("lang").addEventListener("click",function(){S.lang=S.lang==="ar"?"en":"ar";store("lang",S.lang);chrome();if(S.data)render()});
$("addMeter").addEventListener("click",function(){openMeter(null)});
$("export").addEventListener("click",function(){location.href="/api/export?"+new URLSearchParams({type:S.type,month:S.month})});
$("building").addEventListener("change",function(){S.building=this.value;S.page=1;load()});
var qT;$("q").addEventListener("input",function(){var v=this.value;clearTimeout(qT);qT=setTimeout(function(){S.q=v.trim();S.page=1;load()},250)});
refresh();
</script>
</body>
</html>
"""


# ---------- server ----------

class Handler(BaseHTTPRequestHandler):
    server_version = "MeterTracker"
    sys_version = ""

    def log_message(self, fmt, *args):
        pass

    def send_bytes(self, code, data, ctype, headers=None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        for key, value in (headers or {}).items():
            self.send_header(key, value)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(data)

    def send_json(self, code, payload):
        self.send_bytes(code, json.dumps(payload, ensure_ascii=False).encode("utf-8"),
                        "application/json; charset=utf-8", {"Cache-Control": "no-store"})

    def send_page(self, text, code=200, headers=None):
        all_headers = {"Cache-Control": "no-store"}
        all_headers.update(headers or {})
        self.send_bytes(code, text.encode("utf-8"), "text/html; charset=utf-8", all_headers)

    def redirect(self, cookie=None):
        self.send_response(303)
        self.send_header("Location", "/")
        self.send_header("Content-Length", "0")
        if cookie:
            self.send_header("Set-Cookie", cookie)
        self.end_headers()

    def signed_in(self):
        if not APP_PASSWORD:
            return True
        raw = self.headers.get("Cookie", "")
        try:
            jar = SimpleCookie(raw)
        except Exception:
            return False
        return COOKIE_NAME in jar and token_valid(jar[COOKIE_NAME].value)

    def cookie_text(self, value, max_age):
        secure = "; Secure" if self.headers.get("X-Forwarded-Proto") == "https" else ""
        return f"{COOKIE_NAME}={value}; Path=/; Max-Age={max_age}; HttpOnly; SameSite=Lax{secure}"

    def read_raw(self):
        try:
            length = int(self.headers.get("Content-Length", 0))
        except ValueError:
            length = 0
        if length > MAX_BODY:
            raise BadInput("server")
        return self.rfile.read(length) if length > 0 else b""

    def read_json(self):
        if "application/json" not in self.headers.get("Content-Type", ""):
            raise BadInput("server")
        try:
            data = json.loads(self.read_raw().decode("utf-8") or "{}")
        except (ValueError, UnicodeDecodeError):
            raise BadInput("server")
        if not isinstance(data, dict):
            raise BadInput("server")
        return data

    def login_page(self, message_html="", code=200):
        self.send_page(LOGIN_HTML.replace("__MSG__", message_html), code)

    def serve_logo(self, path):
        name = path[len("/logos/"):]
        stem = name[:-4] if name.endswith(".png") else ""
        file_path = os.path.join(BASE_DIR, "logos", stem + ".png")
        if stem not in LOGO_NAMES or not os.path.isfile(file_path):
            self.send_bytes(404, b"", "text/plain")
            return
        with open(file_path, "rb") as f:
            self.send_bytes(200, f.read(), "image/png", {"Cache-Control": "public, max-age=3600"})

    def guarded(self, action):
        try:
            action()
        except BadInput as e:
            self.send_json(400, {"error": str(e)})
        except DuplicateKeyError:
            self.send_json(409, {"error": "dup_meter"})
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception:
            traceback.print_exc()
            self.send_json(500, {"error": "server"})

    def need_api(self):
        if not self.signed_in():
            self.send_json(401, {"error": "server"})
            return False
        if meters is None:
            self.send_json(500, {"error": "server"})
            return False
        return True

    def do_HEAD(self):
        self.do_GET()

    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path
        query = {k: v[0] for k, v in parse_qs(parsed.query).items()}
        if path.startswith("/logos/"):
            self.serve_logo(path)
        elif path == "/":
            if self.signed_in():
                page = INDEX_HTML
                if not APP_PASSWORD:
                    page = page.replace('<form method="post" action="/logout"', '<form hidden method="post" action="/logout"')
                self.send_page(page)
            else:
                self.login_page()
        elif not path.startswith("/api/"):
            self.send_bytes(404, b"Not found", "text/plain")
        elif self.need_api():
            self.guarded(lambda: self.get_api(path, query))

    def get_api(self, path, query):
        if path == "/api/list":
            self.send_json(200, list_view(query))
        elif path == "/api/history":
            self.send_json(200, meter_history(clean(query.get("meter_id"), 40)))
        elif path == "/api/export":
            data = export_csv(query)
            name = f"{query['type']}-meters-{query['month']}.csv"
            self.send_bytes(200, data, "text/csv; charset=utf-8", {
                "Content-Disposition": f'attachment; filename="{name}"',
                "Cache-Control": "no-store",
            })
        else:
            self.send_json(404, {"error": "server"})

    def do_POST(self):
        path = urlparse(self.path).path
        if path == "/login":
            self.handle_login()
        elif path == "/logout":
            self.redirect(self.cookie_text("", 0))
        elif self.need_api():
            self.guarded(lambda: self.post_api(path))

    def handle_login(self):
        if login_locked():
            self.login_page('<p class="e">محاولات كثيرة. انتظر 5 دقائق | Too many attempts. Wait 5 minutes.</p>', 429)
            return
        try:
            form = parse_qs(self.read_raw().decode("utf-8"))
        except (BadInput, UnicodeDecodeError):
            form = {}
        typed = form.get("password", [""])[0]
        if APP_PASSWORD and hmac.compare_digest(typed.encode("utf-8"), APP_PASSWORD.encode("utf-8")):
            self.redirect(self.cookie_text(make_token(), SESSION_SECONDS))
            return
        note_failed_login()
        time.sleep(0.7)
        self.login_page('<p class="e">' + html.escape("كلمة المرور غير صحيحة | Wrong password") + "</p>", 401)

    def post_api(self, path):
        transfer = re.fullmatch(r"/api/meters/([^/]+)/transfer", path)
        if transfer:
            change_transfer(transfer.group(1), self.read_json())
            self.send_json(200, {"ok": True})
            return
        if path != "/api/meters":
            self.send_json(404, {"error": "server"})
            return
        body = self.read_json()
        doc = meter_fields(body)
        doc["type"] = check_type(body.get("type"))
        doc["id"] = uuid.uuid4().hex
        doc["created"] = datetime.now(timezone.utc).isoformat()
        doc["number_log"] = []
        meters.insert_one(doc)
        doc.pop("_id", None)
        self.send_json(201, {"meter": doc})

    def do_PUT(self):
        path = urlparse(self.path).path
        if self.need_api():
            self.guarded(lambda: self.put_api(path))

    def put_api(self, path):
        body = self.read_json()
        if path == "/api/bills":
            save_bill(body)
            self.send_json(200, {"ok": True})
        elif path.startswith("/api/meters/"):
            update_meter(path.rsplit("/", 1)[1], body)
            self.send_json(200, {"ok": True})
        else:
            self.send_json(404, {"error": "server"})

    def do_DELETE(self):
        parsed = urlparse(self.path)
        if self.need_api():
            self.guarded(lambda: self.delete_api(parsed))

    def delete_api(self, parsed):
        path = parsed.path
        log_entry = re.fullmatch(r"/api/meters/([^/]+)/log/([^/]+)", path)
        if log_entry:
            meters.update_one(
                {"id": log_entry.group(1)},
                {"$pull": {"number_log": {"id": log_entry.group(2)}}},
            )
            self.send_json(200, {"ok": True})
        elif path.startswith("/api/meters/"):
            meter_id = path.rsplit("/", 1)[1]
            bills.delete_many({"meter_id": meter_id})
            meters.delete_one({"id": meter_id})
            self.send_json(200, {"ok": True})
        elif path == "/api/bills":
            query = {k: v[0] for k, v in parse_qs(parsed.query).items()}
            bills.delete_one({
                "meter_id": clean(query.get("meter_id"), 40),
                "period": check_period(query.get("period", "")),
            })
            self.send_json(200, {"ok": True})
        else:
            self.send_json(404, {"error": "server"})


if __name__ == "__main__":
    ensure_indexes()
    port = int(os.environ.get("PORT", 8000))
    print(f"Running on port {port}")
    ThreadingHTTPServer(("0.0.0.0", port), Handler).serve_forever()
