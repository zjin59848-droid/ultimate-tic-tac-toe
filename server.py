# -*- coding: utf-8 -*-
"""
超级井字棋 · 局域网联机服务器
- HTTP  : 提供 index.html 与自检页 /check（端口 N）
- WS    : 房间/座位/落子同步（端口 N+1）
- 规则  : 服务端权威判定，客户端只负责渲染
用法: python server.py [--port 8321] [--no-open]
"""
from __future__ import annotations

import argparse
import asyncio
import json
import os
import random
import socket
import sys
import threading
import time
import urllib.parse
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ---------------------------------------------------------------- 游戏规则
LINES = [(0, 1, 2), (3, 4, 5), (6, 7, 8),
         (0, 3, 6), (1, 4, 7), (2, 5, 8),
         (0, 4, 8), (2, 4, 6)]
NAMES = ["左上", "正上", "右上", "左中", "中央", "右中", "左下", "正下", "右下"]
CODE_ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"  # 去掉易混淆的 I/O/0/1
ROOM_TTL = 1800  # 空房间 30 分钟后回收


def new_game() -> dict:
    return {
        "boards": [[None] * 9 for _ in range(9)],
        "status": [None] * 9,
        "winLines": [None] * 9,
        "active": None,
        "current": "X",
        "majorLine": None,
        "gameOver": False,
        "winner": None,
        "lastMove": None,
        "score": {"X": 0, "O": 0, "draw": 0},
        "round": 1,
    }


def find_win(arr):
    for a, b, c in LINES:
        v = arr[a]
        if v and v != "draw" and v == arr[b] == arr[c]:
            return [a, b, c]
    return None


def can_play(g: dict, seat, b, i):
    """返回 None 表示合法，否则返回错误文案。seat=None 表示观战者。"""
    if g["gameOver"]:
        return "本局已结束，等待玩家开始新对局"
    if seat is None:
        return "观战中，先选择座位才能落子"
    if seat != g["current"]:
        return "还没轮到你"
    if not (isinstance(b, int) and isinstance(i, int) and 0 <= b < 9 and 0 <= i < 9):
        return "非法落点"
    if g["active"] is not None and g["active"] != b:
        return f"必须在「{NAMES[g['active']]}」小棋盘落子"
    if g["status"][b] is not None:
        return "该小棋盘已经结束"
    if g["boards"][b][i] is not None:
        return "该格已经有棋子"
    return None


def apply_move(g: dict, b: int, i: int) -> None:
    """执行落子并推进状态（与前端逻辑一致，已通过随机对局验证）。"""
    cur = g["current"]
    g["boards"][b][i] = cur
    g["lastMove"] = {"b": b, "i": i, "p": cur}

    line = find_win(g["boards"][b])
    if line:
        g["status"][b] = cur
        g["winLines"][b] = line
    elif all(v is not None for v in g["boards"][b]):
        g["status"][b] = "draw"

    g["majorLine"] = find_win(g["status"])
    if g["majorLine"]:
        g["gameOver"] = True
        g["winner"] = cur
        g["score"][cur] += 1
        return

    if all(s is not None for s in g["status"]):
        g["gameOver"] = True
        g["winner"] = None
        g["score"]["draw"] += 1
        return

    g["active"] = i if g["status"][i] is None else None
    g["current"] = "O" if cur == "X" else "X"


# ---------------------------------------------------------------- 作弊/测试工具
def recompute_major(g: dict) -> None:
    """按 status 重新判定大棋盘（不切换回合，专供测试指令）。"""
    if g["gameOver"]:
        return
    g["majorLine"] = find_win(g["status"])
    if g["majorLine"]:
        winner = next((g["status"][i] for i in g["majorLine"]
                       if g["status"][i] not in (None, "draw")), None)
        if winner:
            g["gameOver"] = True
            g["winner"] = winner
            g["score"][winner] += 1
            return
    if all(s is not None for s in g["status"]):
        g["gameOver"] = True
        g["winner"] = None
        g["score"]["draw"] += 1


def force_place(g: dict, b: int, i: int, seat: str) -> None:
    g["boards"][b][i] = seat
    g["lastMove"] = {"b": b, "i": i, "p": seat}
    if g["status"][b] is None:
        line = find_win(g["boards"][b])
        if line:
            g["status"][b] = seat
            g["winLines"][b] = line
        elif all(v is not None for v in g["boards"][b]):
            g["status"][b] = "draw"
    recompute_major(g)


def force_claim(g: dict, b: int, seat: str) -> None:
    """直接占领小棋盘（必要时补一条三连线，让画面可信）。"""
    line = find_win(g["boards"][b])
    if not line:
        for cells in ((0, 1, 2), (0, 4, 8), (3, 4, 5)):
            if all(g["boards"][b][c] in (None, seat) for c in cells):
                for c in cells:
                    g["boards"][b][c] = seat
                line = list(cells)
                break
    g["status"][b] = seat
    if line:
        g["winLines"][b] = line
        g["lastMove"] = {"b": b, "i": line[-1], "p": seat}
    recompute_major(g)


def reset_sub(g: dict, b: int) -> None:
    prev_winner = g["winner"]
    g["boards"][b] = [None] * 9
    g["status"][b] = None
    g["winLines"][b] = None
    g["majorLine"] = find_win(g["status"])
    if g["gameOver"] and prev_winner in ("X", "O") and g["majorLine"] is None:
        g["gameOver"] = False
        g["winner"] = None
        g["score"][prev_winner] = max(0, g["score"].get(prev_winner, 0) - 1)


def cheat_restart(g: dict) -> dict:
    """保留比分、重开一局，返回新 game。"""
    sc, rr = dict(g["score"]), g["round"]
    ng = new_game()
    ng["score"] = sc
    ng["round"] = rr
    return ng


def cheat_claim_many(g: dict, seat: str, boards: list) -> None:
    for b in boards:
        force_claim(g, b, seat)


def cheat_to_hot(g: dict, seat: str) -> bool:
    """把落子格数推到 ≥12（触发白热化）且不结束对局。
    先占 3 个不构成三连的小盘（画面好看），再往已定胜负的盘里补格子到 12。"""
    guard = 0
    while sum(1 for s in g["status"] if s == seat) < 3 and guard < 9:
        guard += 1
        pick = None
        for b in range(9):
            if g["status"][b] is not None:
                continue
            trial = list(g["status"])
            trial[b] = seat
            if find_win(trial) is None:
                pick = b
                break
        if pick is None:
            break
        force_claim(g, pick, seat)

    def filled() -> int:
        return sum(1 for row in g["boards"] for v in row if v)

    if filled() >= 12:
        return True
    # 往「已定胜负」的盘里直接补格子：不触发重判，也就不会误判胜负
    decided = [i for i, s in enumerate(g["status"]) if s is not None]
    owned = [i for i in decided if g["status"][i] == seat]
    for b in owned + [i for i in decided if i not in owned]:
        for i in range(9):
            if g["boards"][b][i] is None:
                g["boards"][b][i] = seat
                g["lastMove"] = {"b": b, "i": i, "p": seat}
                if filled() >= 12:
                    return True
    return filled() >= 12


# ---------------------------------------------------------------- 房间模型
class Client:
    __slots__ = ("ws", "cid", "room", "seat", "name_hint")

    def __init__(self, ws, cid=None):
        self.ws = ws
        self.cid = cid or uuid.uuid4().hex
        self.room = None
        self.seat = None  # "X" | "O" | None(观战)
        self.name_hint = ""  # 客户端带来的昵称（进房时携带）


class Room:
    __slots__ = ("code", "game", "seats", "conns", "share", "qr", "last_active",
                 "owner", "members", "names", "tokens", "banned", "offline")

    def __init__(self, code, share="", qr="", owner=None):
        self.code = code
        self.game = new_game()
        self.seats = {"X": None, "O": None}   # 座位 -> 客户端 cid（90 秒断线保留）
        self.conns = {}                        # ws -> Client（仅在线）
        self.share = share
        self.qr = qr
        self.last_active = time.time()
        self.owner = owner        # 房主 cid
        self.members = {}         # cid -> True（含离线，可被踢）
        self.names = {}           # cid -> 昵称
        self.tokens = {}          # cid -> 踢人/转让令牌（仅下发给房主）
        self.banned = set()       # 被踢出、禁止再进的 cid
        self.offline = {}         # cid -> 断线时间（座位保留计时）


ROOMS: dict[str, Room] = {}
WS_CONNS: dict = {}   # ws -> Client


def new_code() -> str:
    while True:
        code = "".join(random.choice(CODE_ALPHABET) for _ in range(6))
        if code not in ROOMS:
            return code


def lan_ips() -> list[str]:
    ips: list[str] = []
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ips.append(s.getsockname()[0])
        s.close()
    except Exception:
        pass
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ip = info[4][0]
            if ip not in ips and not ip.startswith("127."):
                ips.append(ip)
    except Exception:
        pass
    private = [i for i in ips if i.startswith(("192.168.", "10.", "172."))]
    ordered = private + [i for i in ips if i not in private]
    return ordered or ["127.0.0.1"]


def qr_svg(data: str) -> str:
    """生成二维码 SVG（供邀请面板显示），失败时返回空串。"""
    try:
        import qrcode
        from qrcode.image.svg import SvgPathImage
        qr = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M,
                           box_size=8, border=2)
        qr.add_data(data)
        qr.make(fit=True)
        img = qr.make_image(image_factory=SvgPathImage)
        raw = img.to_string() if hasattr(img, "to_string") else str(img)
        if isinstance(raw, bytes):
            raw = raw.decode("utf-8", "replace")
        return raw if raw.lstrip().startswith("<svg") else ""
    except Exception:
        return ""


# ---------------------------------------------------------------- 成员与身份
NICK_POOL = ["小火箭", "薄荷糖", "小南瓜", "流星", "布丁", "小狐狸", "汽水",
             "板栗", "团子", "小海豚", "芝麻", "小柚子", "闪电", "蘑菇",
             "汤圆", "铃铛", "小樱桃", "芋圆"]


def clean_name(raw) -> str:
    """昵称清洗：可打印字符、去首尾空白、最多 8 字。"""
    if raw is None:
        return ""
    s = "".join(ch for ch in str(raw) if ch.isprintable()).strip()
    return s[:8]


def unique_nick(room: Room) -> str:
    used = set(room.names.values())
    for base in random.sample(NICK_POOL, len(NICK_POOL)):
        if base not in used:
            return base
    return "玩家" + uuid.uuid4().hex[:4]


def ensure_identity(room: Room, client: Client):
    """进房：登记成员、分配令牌、恢复/生成昵称、清除离线计时。"""
    room.members[client.cid] = True
    room.tokens.setdefault(client.cid, uuid.uuid4().hex[:12])
    room.offline.pop(client.cid, None)
    if client.name_hint:
        room.names[client.cid] = client.name_hint
    elif client.cid not in room.names:
        room.names[client.cid] = unique_nick(room)


def member_by_token(room: Room, token: str):
    return next((c for c, tk in room.tokens.items()
                 if tk == token and c in room.members), None)


def remove_member(room: Room, cid: str, banned: bool = False) -> str:
    """移除成员并释放座位，返回其昵称。"""
    for seat, holder in list(room.seats.items()):
        if holder == cid:
            room.seats[seat] = None
    nick = room.names.pop(cid, "")
    room.members.pop(cid, None)
    room.tokens.pop(cid, None)
    room.offline.pop(cid, None)
    if banned:
        room.banned.add(cid)
    return nick


# ---------------------------------------------------------------- 消息处理
async def send(ws, obj: dict):
    try:
        await ws.send(json.dumps(obj, ensure_ascii=False))
    except Exception:
        pass


async def notice(room: Room, msg: str, exclude=None):
    for ws2, c2 in list(room.conns.items()):
        if exclude is not None and c2.cid == exclude:
            continue
        await send(ws2, {"type": "notice", "msg": msg})


def member_list(room: Room, viewer: Client) -> list[dict]:
    seat_of = {cid: s for s, cid in room.seats.items() if cid}
    online = {c.cid for c in room.conns.values()}
    is_owner = viewer.cid == room.owner
    out = []
    for cid in room.members:
        m = {
            "nick": room.names.get(cid, "玩家"),
            "seat": seat_of.get(cid),
            "online": cid in online,
            "owner": cid == room.owner,
            "self": cid == viewer.cid,
        }
        if is_owner and cid != viewer.cid:
            # 只有房主能拿到别人的 cid / 令牌，其他人看不到
            m["cid"] = cid
            m["token"] = room.tokens.get(cid, "")
        out.append(m)
    order = {"X": 0, "O": 1}
    out.sort(key=lambda m: (order.get(m["seat"], 2), m["nick"]))
    return out


def state_payload(room: Room, client: Client) -> dict:
    return {
        "type": "state",
        "room": room.code,
        "you": client.seat or "watch",
        "nick": room.names.get(client.cid, ""),
        "isOwner": client.cid == room.owner,
        "members": member_list(room, client),
        "seats": {k: bool(v) for k, v in room.seats.items()},
        "watch": sum(1 for c in room.conns.values() if c.seat is None),
        "share": room.share,
        "qr": room.qr,
        "lanUrl": room.share,
        "cheat": bool(CFG.get("cheat")),
        "game": room.game,
    }


async def broadcast(room: Room):
    room.last_active = time.time()
    for ws, client in list(room.conns.items()):
        await send(ws, state_payload(room, client))


def auto_seat(room: Room, client: Client):
    if client.seat:
        return
    for seat in ("X", "O"):
        if room.seats[seat] is None or room.seats[seat] == client.cid:
            room.seats[seat] = client.cid
            client.seat = seat
            return
    client.seat = None  # 两座已满 -> 观战


def join_room(room: Room, client: Client, auto: bool = True):
    if client.room and client.room is not room and client.ws in client.room.conns:
        client.room.conns.pop(client.ws, None)
        client.room.offline[client.cid] = time.time()
    client.room = room
    room.conns[client.ws] = client
    # 按 cid 找回自己的座位（刷新/重连不掉座）
    client.seat = next((s for s, cid in room.seats.items() if cid == client.cid), None)
    ensure_identity(room, client)   # 登记成员 + 昵称 + 清除离线计时
    if auto:
        auto_seat(room, client)


async def dispatch(client: Client, data: dict):
    ws = client.ws
    t = data.get("type")

    if t == "hello":
        cid = data.get("cid")
        if isinstance(cid, str) and 4 <= len(cid) <= 64:
            client.cid = cid
        client.name_hint = clean_name(data.get("name"))
        code = str(data.get("room") or "").strip().upper()
        room = ROOMS.get(code)
        if room and client.cid in room.banned:
            await send(ws, {"type": "kicked",
                            "msg": "你已被房主移出该房间，无法再加入"})
            return
        if room:
            join_room(room, client, auto=False)
            await broadcast(room)
        else:
            if code:
                await send(ws, {"type": "error", "msg": f"房间 {code} 不存在，可能已关闭"})
            await send(ws, {"type": "lobby"})

    elif t == "create":
        code = new_code()
        ip = lan_ips()[0]
        share = f"http://{ip}:{CFG['port']}/?room={code}"
        room = Room(code, share=share, qr=qr_svg(share), owner=client.cid)
        ROOMS[code] = room
        client.name_hint = clean_name(data.get("name"))
        join_room(room, client, auto=True)
        await broadcast(room)

    elif t == "join":
        code = str(data.get("room") or "").strip().upper()
        room = ROOMS.get(code)
        if not room:
            await send(ws, {"type": "error", "msg": f"房间 {code} 不存在，请核对房间码"})
            return
        if client.cid in room.banned:
            await send(ws, {"type": "kicked",
                            "msg": "你已被房主移出该房间，无法再加入"})
            return
        client.name_hint = clean_name(data.get("name"))
        join_room(room, client, auto=True)
        await broadcast(room)

    elif t == "seat":
        room = client.room
        if not room:
            await send(ws, {"type": "error", "msg": "你还不在任何房间里"})
            return
        want = data.get("seat")
        prev = client.seat
        nick = room.names.get(client.cid, "玩家")
        if want == "watch":
            if prev is None:
                await send(ws, {"type": "notice", "msg": "你已经在观战了"})
                return
            for s, cid in list(room.seats.items()):
                if cid == client.cid:
                    room.seats[s] = None
            client.seat = None
            await send(ws, {"type": "notice", "msg": f"你已下台观战，{prev} 座位已空出"})
            await notice(room, f"「{nick}」下台观战（{prev} 座空出）", exclude=client.cid)
        elif want in ("X", "O"):
            holder = room.seats[want]
            if holder is not None and holder != client.cid:
                await send(ws, {"type": "error", "msg": f"{want} 座位已被占用"})
                return
            for s, cid in list(room.seats.items()):
                if cid == client.cid:
                    room.seats[s] = None
            room.seats[want] = client.cid
            client.seat = want
            if prev != want:
                await send(ws, {"type": "notice",
                                "msg": (f"你已上台执 {want}，继续当前对局"
                                        if prev is None else f"你已换到 {want} 座位")})
                await notice(room, f"「{nick}」上台执 {want}", exclude=client.cid)
        else:
            await send(ws, {"type": "error", "msg": "未知座位"})
            return
        await broadcast(room)

    elif t == "name":
        room = client.room
        if not room:
            await send(ws, {"type": "error", "msg": "你还不在任何房间里"})
            return
        nick = clean_name(data.get("name"))
        if not nick:
            await send(ws, {"type": "error", "msg": "昵称不能为空（最多 8 个字）"})
            return
        room.names[client.cid] = nick
        client.name_hint = nick
        await broadcast(room)

    elif t == "kick":
        room = client.room
        if not room:
            await send(ws, {"type": "error", "msg": "你还不在任何房间里"})
            return
        if room.owner != client.cid:
            await send(ws, {"type": "error", "msg": "只有房主可以踢人"})
            return
        target = member_by_token(room, str(data.get("token") or ""))
        if not target or target == client.cid:
            await send(ws, {"type": "error", "msg": "无效的成员"})
            return
        owner_nick = room.names.get(client.cid, "房主")
        nick = remove_member(room, target, banned=True)
        for ws2, c2 in list(room.conns.items()):
            if c2.cid == target:
                room.conns.pop(ws2, None)
                c2.room = None
                c2.seat = None
                await send(ws2, {"type": "kicked",
                                 "msg": f"你已被房主「{owner_nick}」移出该房间"})
        await notice(room, f"房主踢出了「{nick}」")
        await broadcast(room)

    elif t == "transfer":
        room = client.room
        if not room:
            await send(ws, {"type": "error", "msg": "你还不在任何房间里"})
            return
        if room.owner != client.cid:
            await send(ws, {"type": "error", "msg": "只有房主可以转让房主"})
            return
        target = member_by_token(room, str(data.get("token") or ""))
        if not target or target == client.cid:
            await send(ws, {"type": "error", "msg": "无效的成员"})
            return
        room.owner = target
        await notice(room, f"房主已转让给「{room.names.get(target, '玩家')}」")
        await broadcast(room)

    elif t == "move":
        room = client.room
        if not room:
            await send(ws, {"type": "error", "msg": "你还不在任何房间里"})
            return
        g = room.game
        b, i = data.get("b"), data.get("i")
        err = can_play(g, client.seat, b, i)
        if err:
            await send(ws, {"type": "error", "msg": err})
            return
        apply_move(g, b, i)
        await broadcast(room)

    elif t == "again":
        room = client.room
        if not room:
            return
        if client.seat is None:
            await send(ws, {"type": "error", "msg": "观战中不能开局，请先选择座位"})
            return
        prev_round = room.game["round"]
        score = room.game["score"]
        room.game = new_game()
        room.game["score"] = score
        room.game["round"] = prev_round + 1
        await broadcast(room)

    elif t == "reset":
        room = client.room
        if not room:
            return
        if client.seat is None:
            await send(ws, {"type": "error", "msg": "观战中不能重置比分"})
            return
        room.game = new_game()
        await broadcast(room)

    elif t == "cheat":
        if not CFG.get("cheat"):
            await send(ws, {"type": "error",
                            "msg": "作弊模式未开启（启动服务器时加 --cheat）"})
            return
        room = client.room
        if not room:
            await send(ws, {"type": "error", "msg": "你还不在任何房间里"})
            return
        g = room.game
        op = data.get("op")
        seat = data.get("seat") if data.get("seat") in ("X", "O") else g["current"]
        ok = True

        if op == "turn":
            g["current"] = seat

        elif op == "place":
            b, i = data.get("b"), data.get("i")
            if isinstance(b, int) and isinstance(i, int) and 0 <= b < 9 and 0 <= i < 9:
                force_place(g, b, i, seat)
            else:
                ok = False

        elif op == "claim":
            b = data.get("b")
            if isinstance(b, int) and 0 <= b < 9:
                force_claim(g, b, seat)
            else:
                ok = False

        elif op == "clear_sub":
            b = data.get("b")
            if isinstance(b, int) and 0 <= b < 9:
                reset_sub(g, b)
            else:
                ok = False

        elif op == "hot":
            if g["gameOver"]:
                room.game = cheat_restart(g)
                g = room.game
            cheat_to_hot(g, seat)

        elif op == "win":
            if g["gameOver"]:
                room.game = cheat_restart(g)
                g = room.game
            cheat_claim_many(g, seat, [0, 1, 2])

        elif op == "new_game":
            room.game = cheat_restart(g)
            room.game["round"] += 1

        elif op == "score":
            key, delta = data.get("key"), data.get("delta", 0)
            if key in ("X", "O", "draw") and isinstance(delta, int):
                g["score"][key] = max(0, g["score"][key] + delta)
            else:
                ok = False

        elif op == "score_reset":
            g["score"] = {"X": 0, "O": 0, "draw": 0}

        else:
            ok = False

        if not ok:
            await send(ws, {"type": "error", "msg": "未知作弊指令"})
            return
        await broadcast(room)

    elif t == "ping":
        await send(ws, {"type": "pong", "ts": data.get("ts")})


async def ws_handler(ws):
    client = Client(ws)
    WS_CONNS[ws] = client
    try:
        async for message in ws:
            try:
                data = json.loads(message)
            except Exception:
                continue
            if isinstance(data, dict):
                try:
                    await dispatch(client, data)
                except Exception as exc:  # 单条消息出错不影响连接
                    await send(ws, {"type": "error", "msg": f"服务器内部错误: {exc}"})
    except Exception:
        pass
    finally:
        WS_CONNS.pop(ws, None)
        room = client.room
        if room and room.conns.get(ws) is client:
            room.conns.pop(ws, None)
            # 断线：座位保留 seat_grace 秒，超时由 gc_loop 释放
            room.offline[client.cid] = time.time()
            room.last_active = time.time()
            try:
                await broadcast(room)
            except Exception:
                pass


async def gc_loop():
    """巡检：释放超时座位 + 回收空房间（间隔随保留时长自适应）。"""
    interval = max(1, min(10, CFG.get("seat_grace", 90) // 3))
    while True:
        await asyncio.sleep(interval)
        now = time.time()
        for room in list(ROOMS.values()):
            for cid, ts in list(room.offline.items()):
                if now - ts <= CFG.get("seat_grace", 90):
                    continue
                room.offline.pop(cid, None)
                seat = next((s for s, x in room.seats.items() if x == cid), None)
                if seat:
                    room.seats[seat] = None
                # 超时未重连 = 已离开房间：从成员列表移除（未被踢，可随时再进）
                remove_member(room, cid, banned=False)
                try:
                    if seat:
                        await notice(room, f"{seat} 座位已空出（超时未重连）")
                    await broadcast(room)
                except Exception:
                    pass
        for code in [c for c, r in ROOMS.items()
                     if not r.conns and now - r.last_active > ROOM_TTL]:
            ROOMS.pop(code, None)


# ---------------------------------------------------------------- HTTP 静态服务
CFG = {"port": 8321, "ws_port": 8322, "index": "", "seat_grace": 90, "cheat": False}


def resource_path(name: str) -> str:
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, name)


def asset_path(name: str):
    """素材查找：exe 同目录 assets/ 优先（用户放文件即可生效、无需重新打包），
    其次是打包内置的 assets/，最后是源码目录。"""
    candidates = []
    if getattr(sys, "frozen", False):
        candidates.append(os.path.join(os.path.dirname(sys.executable), "assets", name))
    candidates.append(os.path.join(
        getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__))),
        "assets", name))
    candidates.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "assets", name))
    for c in candidates:
        if os.path.isfile(c):
            return c
    return None


def port_listening(host: str, port: int) -> bool:
    """探测端口是否已有服务在监听（比直接 bind 精确，避免 TIME_WAIT 误判）。"""
    probe_host = "127.0.0.1" if host in ("0.0.0.0", "", "::") else host
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.settimeout(0.5)
    try:
        return s.connect_ex((probe_host, port)) == 0
    except Exception:
        return False
    finally:
        s.close()


CHECK_HTML = """<!DOCTYPE html><html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>联机自检</title><style>
body{{background:#0e1120;color:#e8ecff;font-family:"Microsoft YaHei",sans-serif;
padding:24px;line-height:1.9;max-width:640px;margin:0 auto}}
h1{{font-size:22px}} .ok{{color:#4cc9f0}} .warn{{color:#ffd166}}
li{{margin:8px 0}} code{{background:#1e2340;padding:2px 8px;border-radius:6px}}
</style></head><body>
<h1>联机自检页面</h1>
<p class="ok">✅ 如果你能在手机上打开本页，说明网络可达、服务器正常。</p>
<p>本机地址：</p><ul>{urls}</ul>
<p>WebSocket 端口：<code>{ws_port}</code>（由网页自动连接）</p>
<p class="warn">连不上时检查：</p>
<ol>
<li>Windows 防火墙弹窗是否选择了「允许访问」（专用网络）</li>
<li>手机和电脑是否在同一个 WiFi</li>
<li>路由器是否开启了「AP 隔离 / 访客网络」，需在路由器后台关闭</li>
</ol>
<p><a href="/" style="color:#ffd166">← 返回游戏</a></p>
</body></html>"""


class HttpHandler(BaseHTTPRequestHandler):
    server_version = "UltimateTTT/1.0"

    def _send(self, body: bytes, ctype: str, status: int = 200):
        try:
            self.send_response(status)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
            self.end_headers()
            self.wfile.write(body)
        except Exception:
            pass

    def do_GET(self):
        path = urllib.parse.urlparse(self.path).path
        if path in ("/", "/index.html", "/game"):
            try:
                with open(CFG["index"], "rb") as f:
                    self._send(f.read(), "text/html; charset=utf-8")
            except Exception as exc:
                self._send(f"index.html 读取失败: {exc}".encode(), "text/plain; charset=utf-8", 500)
        elif path.startswith("/assets/"):
            # 静态资源（背景图 / 暴风素材 / BGM），只允许纯文件名，防目录穿越
            name = os.path.basename(urllib.parse.unquote(path[len("/assets/"):]))
            fp = asset_path(name) if name else None
            if fp:
                ext = os.path.splitext(name)[1].lower()
                ctype = {".jpg": "image/jpeg", ".jpeg": "image/jpeg",
                         ".png": "image/png", ".webp": "image/webp",
                         ".svg": "image/svg+xml", ".gif": "image/gif",
                         ".mp3": "audio/mpeg", ".ogg": "audio/ogg",
                         ".m4a": "audio/mp4", ".wav": "audio/wav",
                         ".flac": "audio/flac", ".aac": "audio/aac",
                         ".mp4": "video/mp4", ".webm": "video/webm",
                         }.get(ext, "application/octet-stream")
                try:
                    with open(fp, "rb") as f:
                        self._send(f.read(), ctype)
                except Exception:
                    self._send(b"read error", "text/plain", 500)
            else:
                self._send(b"404 Not Found", "text/plain", 404)
        elif path == "/check":
            urls = "".join(
                f"<li><code>http://{ip}:{CFG['port']}/</code></li>" for ip in lan_ips())
            html = CHECK_HTML.format(urls=urls, ws_port=CFG["ws_port"])
            self._send(html.encode(), "text/html; charset=utf-8")
        elif path == "/health":
            self._send(b"ok", "text/plain")
        else:
            self._send(b"404 Not Found", "text/plain; charset=utf-8", 404)

    def log_message(self, fmt, *args):
        if CFG.get("verbose"):
            sys.stdout.write("[http] " + (fmt % args) + "\n")


# ---------------------------------------------------------------- 启动
def print_banner(http_port: int, ws_port: int):
    ips = lan_ips()
    line = "=" * 54
    print(line)
    print("   超级井字棋 · 局域网联机服务已启动")
    print(line)
    for ip in ips:
        print(f"   手机/朋友加入 : http://{ip}:{http_port}/")
    print(f"   本机打开     : http://127.0.0.1:{http_port}/")
    print(f"   网络自检     : http://{ips[0]}:{http_port}/check")
    print(f"   WebSocket 端口: {ws_port}")
    print(f"   座位保留时长 : 断线后 {CFG.get('seat_grace', 90)} 秒内可回座")
    if CFG.get("cheat"):
        print("   [!] 作弊/测试模式已开启：网页里按 Ctrl+Shift+D 打开面板")
    print(line)
    print("   把上面局域网链接发给朋友（或扫码），创建/输入房间码即可对局")
    print("   按 Ctrl+C 退出")
    print(line)
    try:
        import qrcode
        qr = qrcode.QRCode(border=1, box_size=1)
        qr.add_data(f"http://{ips[0]}:{http_port}/")
        qr.make(fit=True)
        qr.print_ascii(invert=True)
    except Exception:
        pass


def main():
    global CFG
    # 控制台可能是 GBK：保留原编码但遇到无法编码的字符时替换，绝不崩溃
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding=stream.encoding or "utf-8", errors="replace")
        except Exception:
            pass

    ap = argparse.ArgumentParser(description="超级井字棋局域网联机服务器")
    ap.add_argument("--port", type=int, default=8321, help="HTTP 端口（WS 用 port+1）")
    ap.add_argument("--host", default="0.0.0.0", help="监听地址")
    ap.add_argument("--no-open", action="store_true", help="不自动打开浏览器")
    ap.add_argument("--verbose", action="store_true", help="打印 HTTP 访问日志")
    ap.add_argument("--seat-grace", type=int, default=90, metavar="秒",
                    help="断线后座位保留时长（默认 90 秒）")
    ap.add_argument("--cheat", action="store_true",
                    help="启用作弊/测试模式（网页按 Ctrl+Shift+D 呼出面板）")
    args = ap.parse_args()

    if sys.version_info < (3, 9):
        print("需要 Python 3.9+"); sys.exit(1)

    try:
        import websockets  # noqa: F401
    except Exception as exc:
        print(f"缺少依赖 websockets，请先执行: pip install -r requirements.txt\n{exc}")
        sys.exit(1)

    try:
        from websockets.asyncio.server import serve as ws_serve
    except ImportError:
        from websockets.server import serve as ws_serve

    CFG["port"] = args.port
    CFG["ws_port"] = args.port + 1
    CFG["index"] = resource_path("index.html")
    CFG["verbose"] = args.verbose
    CFG["seat_grace"] = max(1, args.seat_grace)
    CFG["cheat"] = bool(args.cheat)

    if not os.path.exists(CFG["index"]):
        print(f"找不到 index.html（{CFG['index']}）")
        sys.exit(1)

    # 启动前先探测端口：Windows 下 HTTP 可能因 SO_REUSEADDR “看似绑定成功”，
    # 结果到 WebSocket 阶段才报错、信息还容易让用户困惑 —— 这里提前拦截并说人话。
    busy = [p for p in (args.port, args.port + 1) if port_listening(args.host, p)]
    if busy:
        ports = " / ".join(str(p) for p in busy)
        print("=" * 54)
        print(f"  启动失败：端口 {ports} 已被占用")
        print("  原因：已经有一个「超级井字棋」正在运行，")
        print("        或该端口被其它程序占用。")
        print("  处理：关闭正在运行的黑色控制台窗口后重试；")
        print(f"        或换端口启动：超级井字棋.exe --port 9000")
        print("=" * 54)
        sys.exit(1)

    # HTTP 线程
    try:
        httpd = ThreadingHTTPServer((args.host, args.port), HttpHandler)
    except OSError as exc:
        print(f"端口 {args.port} 启动失败: {exc}（是否已启动过？）")
        sys.exit(1)
    threading.Thread(target=httpd.serve_forever, daemon=True).start()

    def _open_browser():
        time.sleep(0.6)
        try:
            import webbrowser
            webbrowser.open(f"http://127.0.0.1:{args.port}/")
        except Exception:
            pass

    async def run():
        asyncio.create_task(gc_loop())
        try:
            async with ws_serve(ws_handler, args.host, CFG["ws_port"], max_size=2 ** 20):
                # 两个端口都就绪后才打印横幅 / 打开浏览器
                print_banner(args.port, CFG["ws_port"])
                if not args.no_open:
                    threading.Thread(target=_open_browser, daemon=True).start()
                await asyncio.Future()
        except OSError as exc:
            print("=" * 54)
            print(f"  启动失败：WebSocket 端口 {CFG['ws_port']} 无法绑定")
            print(f"  原因: {exc}")
            print("  提示：可能已经启动过一个实例，或端口被其它程序占用。")
            print(f"  换个端口试试: {'超级井字棋.exe'} --port 9000")
            print("=" * 54)
            sys.exit(1)

    try:
        asyncio.run(run())
    except KeyboardInterrupt:
        print("\n已退出")
    finally:
        httpd.shutdown()


if __name__ == "__main__":
    main()
