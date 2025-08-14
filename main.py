#!/usr/bin/env python3
import asyncio, json, os, random, textwrap, time
from pathlib import Path
import yaml
from aiohttp import web

# ---------------- paths & data ----------------
ROOT = Path(__file__).parent
DATA = ROOT / "data"
SAVES = ROOT / "saves"
SAVES.mkdir(exist_ok=True)

# ---------------- timing & combat pacing ----------------
TICK_SECONDS = 1.0                 # global heartbeat tick
OUT_OF_COMBAT_SECONDS = 10         # time since last hit to drop combat
DEATH_RESPAWN_SECONDS = 15         # auto-respawn after death
MOB_AI_PERIOD = 3                  # seconds between a mob's turns
MOB_AI_JITTER = 1                  # +/- jitter added to period
PLAYER_AUTO_SWING = 2.5            # seconds between auto-attacks from 'kill'
PLAYER_MOVE_Cancels_AUTO = True

# ---- input normalization / direction aliases ----
DIR_ALIASES = {
    'n': 'north', 's': 'south', 'e': 'east', 'w': 'west',
    'ne': 'northeast', 'nw': 'northwest', 'se': 'southeast', 'sw': 'southwest',
    'u': 'up', 'd': 'down'
}
FULL_DIRS = {'north','south','east','west','northeast','northwest','southeast','southwest','up','down'}

def normalize_cmd(line: str):
    line = (line or '').strip()
    parts = line.split()
    if not parts:
        return '', []
    verb = parts[0].lower()
    args = parts[1:]

    # If user typed a bare direction -> convert to "go <dir>"
    if verb in DIR_ALIASES:
        return 'go', [DIR_ALIASES[verb]]
    if verb in FULL_DIRS:
        return 'go', [verb]

    # If they typed "go se" or "go SE", normalize the arg
    if verb == 'go' and args:
        d = args[0].lower()
        if d in DIR_ALIASES:
            args[0] = DIR_ALIASES[d]
        elif d in FULL_DIRS:
            args[0] = d
    return verb, args

# --------------- helpers ---------------
def wrap(s, width=90):
    return "\n".join(textwrap.fill(line, width) for line in s.splitlines())

def clamp(x, lo, hi):
    return max(lo, min(hi, x))

def load_yaml(name):
    p = DATA / name
    if not p.exists():
        print(f"[WARN] Missing {p}")
        return {}
    try:
        with open(p, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)
            return data or {}
    except Exception as e:
        print(f"[YAML ERROR] {name}: {e}")
        return {}

def norm(s):  # case-insensitive key
    return (s or "").strip().lower()

# Load data once at startup
WORLD = load_yaml('world.yaml')
RACES = load_yaml('races.yaml')
CLASSES = load_yaml('classes.yaml')
DEITIES = load_yaml('deities.yaml')
NPCS = load_yaml('npcs.yaml')
MONSTERS = load_yaml('monsters.yaml')
QUESTS = load_yaml('quests.yaml')
ITEMS = load_yaml('items.yaml')
SHOPS = load_yaml('shops.yaml')

# --------------- state ---------------
PLAYERS = {}         # ws -> Player
ROOM_INSTANCES = {}  # room_id -> {"mobs":[Mob], "dead_at":{Mob:ts}}
ROOM_GROUND = {}     # room_id -> [item_name,...] (loose loot on the ground)

# --------------- models ---------------
class Effect:
    """
    kind: 'dot' | 'hot' | 'buff' | (optionally others)
    For 'buff', use eff.mod to apply temporary deltas (e.g., {'power': +10})
    """
    def __init__(self, name, kind, amount=0, duration=0, tick=0, mod=None, source=None):
        self.name=name; self.kind=kind; self.amount=amount
        self.duration=max(0, int(duration)); self.remaining=self.duration
        self.tick = max(1, int(tick or 1)); self.next_tick_in=self.tick
        self.mod = mod or {}; self.source=source

    def on_tick(self, target):
        msgs=[]
        if self.kind=='dot':
            target.hp = clamp(target.hp - self.amount, 0, target.max_hp)
            msgs.append(f"{target.name} suffers {self.amount} damage from {self.name}.")
            target.flag_combat()
        elif self.kind=='hot':
            healed = clamp(self.amount, 0, target.max_hp - target.hp)
            target.hp += healed
            msgs.append(f"{target.name} heals {healed} from {self.name}.")
        # buffs do not "tick"; they apply on add and are removed on expiry
        self.next_tick_in = self.tick
        return msgs

class Entity:
    def __init__(self, name, room):
        self.name=name; self.room=room
        self.max_hp=100; self.hp=100
        self.power=10; self.defense=0; self.shield=0
        self.alive=True
        self.effects=[]
        self.last_combat_ts=0

    def flag_combat(self):
        self.last_combat_ts = time.time()

    @property
    def in_combat(self):
        if self.last_combat_ts==0: return False
        return (time.time() - self.last_combat_ts) < OUT_OF_COMBAT_SECONDS

    def apply_damage(self, dmg):
        absorbed=0
        if self.shield>0:
            absorbed=min(self.shield, dmg)
            self.shield-=absorbed; dmg-=absorbed
        self.hp = clamp(self.hp - max(0, dmg), 0, self.max_hp)
        if self.hp<=0 and self.alive:
            self.alive=False
        self.flag_combat()
        return absorbed

    def apply_mods(self, mods):
        """Apply temporary deltas to scalar attributes (e.g., power/defense/max_hp/shield)."""
        for k, v in (mods or {}).items():
            setattr(self, k, getattr(self, k, 0) + v)
        if 'max_hp' in (mods or {}):
            self.hp = clamp(self.hp, 0, self.max_hp)

    def remove_mods(self, mods):
        for k, v in (mods or {}).items():
            setattr(self, k, getattr(self, k, 0) - v)
        if 'max_hp' in (mods or {}):
            self.hp = clamp(self.hp, 0, self.max_hp)

    def add_effect(self, eff):
        self.effects.append(eff)
        # Apply buffs immediately (and any modded effect)
        if eff.mod and eff.kind in ('buff',):
            self.apply_mods(eff.mod)
        self.flag_combat()

class Player(Entity):
    def __init__(self, ws, ip):
        super().__init__(name="", room="trade_district")
        self.ws=ws; self.ip=ip
        self.race=None; self.cls=None; self.deity=None
        self.level=1; self.xp=0; self.obols=0
        self.inventory=[]; self.cooldowns={}; self.flags={"created":False,"az_used":False}
        self.target=None; self.quest=None
        self.equipment={'weapon':None,'set':None,'shield':None}
        # primary stats
        self.stats={'STR':10,'INT':10,'DEX':10,'DEF':0,'LCK':10}
        # derived
        self.archetype='Warrior'  # default
        # runtime helpers
        self._dead_since=None
        self._rest_task=None
        self._auto_task=None  # auto-attack task from 'kill'

    def to_json(self):
        return {
            'name': self.name, 'race': self.race, 'cls': self.cls, 'deity': self.deity,
            'room': self.room, 'hp': self.hp, 'max_hp': self.max_hp, 'power': self.power,
            'defense': self.defense, 'shield': self.shield, 'level': self.level, 'xp': self.xp,
            'inventory': self.inventory, 'cooldowns': self.cooldowns, 'flags': self.flags,
            'quest': self.quest, 'equipment': self.equipment, 'stats': self.stats,
            'obols': self.obols, 'archetype': self.archetype
        }

    @property
    def save_path(self):
        return SAVES / f"{(self.name or 'player').lower()}.json"

    # recompute derived stats from base + gear
    def recompute_stats(self):
        base_hp = 100
        base_def = 0
        base_pow = 10

        # class/race mods
        rb = RACES.get(self.race,{}).get('mod',{})
        cb = (CLASSES.get('mods',{}) or {}).get(self.cls,{})
        # gear mods
        wmod = get_item_mods(self.equipment.get('weapon'))
        setmod = get_item_mods(self.equipment.get('set'))
        shmod = get_item_mods(self.equipment.get('shield'))

        # primary stat to power scaling by archetype
        arch = self.archetype
        STR, INT, DEX = self.stats['STR'], self.stats['INT'], self.stats['DEX']

        if arch=='Warrior':
            scaled_power = base_pow + rb.get('power',0) + cb.get('power',0) + (STR//3)
            scaled_def = base_def + rb.get('defense',0) + cb.get('defense',0) + self.stats['DEF']//4
        elif arch=='Mage':
            scaled_power = base_pow + rb.get('power',0) + cb.get('power',0) + (INT//3)
            scaled_def = base_def + rb.get('defense',0) + cb.get('defense',0)
        elif arch=='Rogue':
            scaled_power = base_pow + rb.get('power',0) + cb.get('power',0) + (DEX//3) + (STR//6)
            scaled_def = base_def + rb.get('defense',0) + cb.get('defense',0)
        else: # Healer
            scaled_power = base_pow + rb.get('power',0) + cb.get('power',0) + (INT//4)
            scaled_def = base_def + rb.get('defense',0) + cb.get('defense',0)

        # gear adds
        pow_bonus = wmod.get('power',0) + setmod.get('power',0) + shmod.get('power',0)
        def_bonus = wmod.get('defense',0) + setmod.get('defense',0) + shmod.get('defense',0)
        hp_bonus = wmod.get('hp',0) + setmod.get('hp',0) + shmod.get('hp',0)

        self.power = max(1, scaled_power + pow_bonus)
        self.defense = max(0, scaled_def + def_bonus)
        self.max_hp = max(1, base_hp + rb.get('hp',0) + cb.get('hp',0) + hp_bonus)
        self.hp = clamp(self.hp, 0, self.max_hp)

class Mob(Entity):
    def __init__(self, template_id, room_id):
        if not MONSTERS or not MONSTERS.get('templates'):
            raise ValueError(f"MONSTERS['templates'] not initialized, can't spawn {template_id}")
        if template_id not in MONSTERS['templates']:
            raise ValueError(f"Template '{template_id}' not found in monsters.yaml")
        t = MONSTERS['templates'][template_id]
        super().__init__(name=t['name'], room=room_id)
        self.template_id=template_id
        self.max_hp=t.get('hp',60); self.hp=self.max_hp
        self.power=t.get('power',8); self.defense=t.get('defense',0)
        self.aggro=t.get('aggro',False); self.loot=t.get('loot',[])
        self.respawn=t.get('respawn',45)
        self.skills=t.get('skills',[])  # [{name,type,amount|per_tick,duration,cd}]
        self._skill_cd = {}  # name->seconds
        # AI pacing
        self._ai_cd = random.randint(0, MOB_AI_PERIOD)  # desync mob turns a bit

# --------------- persistence helpers ---------------
def save_player(p: Player):
    try:
        with open(p.save_path, "w", encoding="utf-8") as f:
            json.dump(p.to_json(), f, indent=2)
    except Exception as e:
        print("Save error:", e)

def load_player(name: str):
    path = SAVES / f"{name.lower()}.json"
    if not path.exists():
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        print("Load error:", e)
        return None

# --------------- items helpers ---------------
def get_item_def(item_name):
    if not item_name: return {}
    # try direct, then case-insensitive scan
    d = ITEMS.get(item_name) or ITEMS.get(item_name.strip())
    if d: return d
    q = norm(item_name)
    for k, v in ITEMS.items():
        if norm(k) == q:
            return v
    return {}

def get_item_mods(item_name):
    d=get_item_def(item_name)
    return d.get('mods',{})

def match_item_name(query):
    if not query: return None
    q=norm(query)
    names=list(ITEMS.keys())
    for n in names:
        if norm(n)==q: return n
    for n in names:
        if norm(n).startswith(q): return n
    return None

# --------------- io helpers ---------------
async def send(ws, msg):
    try:
        await ws.send_str(msg)
    except Exception:
        pass

def say_room(room_id, msg, exclude=None):
    for pl in PLAYERS.values():
        if pl.room==room_id and pl.ws is not exclude:
            asyncio.create_task(send(pl.ws, msg))

# --------------- world helpers ---------------
def room(rid):
    return (WORLD.get('rooms') or {}).get(rid)

def room_ground(rid):
    return ROOM_GROUND.setdefault(rid, [])

async def show_room(p: Player):
    r = room(p.room)
    if not r:
        await send(p.ws, "This place does not exist.\n"); return
    title=r['name']; exits=r.get('exits',{})
    players=[q.name for q in PLAYERS.values() if q.room==p.room and q is not p and q.name]
    mobs=[m.name for m in ROOM_INSTANCES.get(p.room,{}).get('mobs',[]) if m.alive]
    ground=room_ground(p.room)
    out=f"\n{title}\n{'-'*len(title)}\n{wrap(r['desc'])}\n"
    # soft nav hints from world "nav" field (optional)
    nav=r.get('nav',{})
    if nav:
        hints=[]
        for d,what in nav.items():
            hints.append(f"{d}: {what}")
        if hints:
            out+=f"From here you glimpse — " + "; ".join(hints) + ".\n"
    if players:
        out+=f"Also here: {', '.join(players)}\n"
    if mobs:
        out+=f"You see: {', '.join(mobs)}\n"
    if ground:
        out+=f"On the ground: {', '.join(ground)}\n"
    if exits:
        out+="Exits: "+", ".join(exits.keys())+"\n"
    await send(p.ws, out)

# --------------- creation (with stats) ---------------
def roll_stats_for_archetype(arch):
    if arch=='Warrior':
        base={'STR':14,'INT':8,'DEX':10,'DEF':6,'LCK':10}
    elif arch=='Mage':
        base={'STR':8,'INT':15,'DEX':10,'DEF':3,'LCK':10}
    elif arch=='Rogue':
        base={'STR':11,'INT':10,'DEX':15,'DEF':4,'LCK':12}
    else: # Healer
        base={'STR':9,'INT':14,'DEX':10,'DEF':4,'LCK':11}
    for k in base:
        base[k]+=random.randint(0,3)
    return base

def archetype_for_class(cls_name):
    arch_map = CLASSES.get('archetype',{}) or {}
    return arch_map.get(cls_name,'Warrior')

def _safe_index(sel, choices):
    try:
        i = int((sel or '1').strip()) - 1
    except Exception:
        i = 0
    return max(0, min(i, len(choices)-1))

async def create_character(p: Player):
    await send(p.ws, "Welcome to Nekhia. Let's forge your fate.\nEnter a name: ")
    nm = await p.ws.receive()
    if nm.type != web.WSMsgType.TEXT:
        return False
    p.name = (nm.data.strip() or 'Wanderer')[:20]

    # Load existing save
    existing = load_player(p.name)
    if existing:
        fields = ["name","race","cls","deity","room","hp","max_hp","power","defense","shield",
                  "level","xp","inventory","flags","quest","equipment","stats","obols","archetype"]
        for k in fields:
            if k in existing:
                setattr(p, k, existing[k])
        p.recompute_stats()
        await send(p.ws, f"\nWelcome back, {p.name}! Resuming your journey.\n")
        await show_room(p)
        return True

    # New character flow
    race_keys=list(RACES.keys())
    await send(p.ws, "\nChoose your race:\n"+"\n".join(f"  {i+1}) {k}" for i,k in enumerate(race_keys))+"\n> ")
    rsel = await p.ws.receive()
    idx  = _safe_index(getattr(rsel, 'data', '1'), race_keys)
    p.race = race_keys[idx]

    # Class by race
    cls_opts = (CLASSES.get('by_race',{}) or {}).get(p.race, [])
    if not cls_opts:
        cls_opts = ["Warrior","Mage","Healer","Rogue"]
    await send(p.ws, f"\nChoose your class ({p.race}):\n"+"\n".join(f"  {i+1}) {k}" for i,k in enumerate(cls_opts))+"\n> ")
    csel = await p.ws.receive()
    cidx = _safe_index(getattr(csel, 'data', '1'), cls_opts)
    p.cls = cls_opts[cidx]
    p.archetype = archetype_for_class(p.cls)

    # Deity
    deities=list((DEITIES or {}).keys())
    if not deities:
        deities=['None']
    await send(p.ws, "\nChoose your deity:\n"+"\n".join(f"  {i+1}) {k}" for i,k in enumerate(deities))+"\n> ")
    dsel = await p.ws.receive()
    didx = _safe_index(getattr(dsel, 'data', '1'), deities)
    p.deity = deities[didx]

    # Stats: roll & set HP baseline then gear calc
    p.stats = roll_stats_for_archetype(p.archetype)
    p.max_hp = 100
    p.hp = p.max_hp
    p.recompute_stats()

    p.flags['created']=True
    p.room='trade_district'
    p.quest={'id':'intro_cult_talisman','stage':0}

    await send(p.ws, f"\nWelcome, {p.name} the {p.race} {p.cls}, devotee of {p.deity}.\n")
    await show_room(p)
    return True

# --------------- abilities & combat ---------------
def ability_defs_for(p: Player):
    acts = (CLASSES.get('abilities',{}) or {}).get(p.cls, [])[:]
    deity = (DEITIES or {}).get(p.deity, {})
    deity_act = deity.get('active') if isinstance(deity, dict) else None
    if deity_act:
        acts.append(deity_act)
    return acts

def try_dodge_block(p: Player):
    # DEX gives dodge chance; DEF stat gives small block
    dodge_chance = min(40, 5 + p.stats['DEX'] // 3)  # %
    if random.randint(1,100) <= dodge_chance:
        return "dodge"
    block_chance = min(25, p.stats['DEF'] // 3)
    if random.randint(1,100) <= block_chance:
        return "block"
    return None

async def cmd_use(p: Player, args):
    if not args:
        await send(p.ws, "Use what?\n"); return
    name=args[0]; target_name=args[1] if len(args)>1 else (p.target or None)
    lname=name.lower()

    # find ability by id or name, case-insensitive
    abil=None
    for a in ability_defs_for(p):
        if a.get('id','').lower()==lname or a.get('name','').lower()==lname:
            abil=a; break
    if not abil:
        await send(p.ws, "Unknown ability.\n"); return

    if abil.get('id') in p.cooldowns:
        await send(p.ws, f"{abil.get('name','Ability')} on cooldown {p.cooldowns[abil['id']]}s.\n"); return

    # target
    target=None
    if target_name:
        tnorm=str(target_name).lower()
        for m in ROOM_INSTANCES.get(p.room,{}).get('mobs',[]):
            if m.alive and m.name.lower().startswith(tnorm):
                target=m; break
        if not target:
            for q in PLAYERS.values():
                if q.room==p.room and q.name and q.name.lower().startswith(tnorm):
                    target=q; break
    if abil.get('target','enemy')=='self':
        target=p
    if not target:
        await send(p.ws, "No valid target.\n"); return

    out=[]; typ=abil.get('type')
    # scale damage by archetype/stat
    scale = 0
    if p.archetype=='Mage':
        scale = p.stats['INT']//4
    elif p.archetype=='Rogue':
        scale = p.stats['DEX']//4
    elif p.archetype=='Healer':
        scale = p.stats['INT']//5
    else:
        scale = p.stats['STR']//4

    power = p.power + abil.get('flat',0) + scale
    if typ=='damage':
        # check target dodge
        if isinstance(target, Player):
            res = try_dodge_block(target)
            if res == "dodge":
                say_room(p.room, f"* {p.name}'s {abil['name']} misses {target.name} (dodged).\n")
                return
            if res == "block":
                say_room(p.room, f"* {target.name} blocks {p.name}'s {abil['name']}.\n")
                return
        dmg=max(0, power + abil.get('amount',0) - getattr(target,'defense',0))
        absorbed=target.apply_damage(dmg)
        out.append(f"You use {abil['name']} on {target.name} for {dmg} ({absorbed} absorbed).")
        if not target.alive and isinstance(target, Mob):
            await mob_death(target, p)
    elif typ=='dot':
        e=Effect(abil['name'],'dot',amount=abil.get('per_tick',5),duration=abil.get('duration',10),tick=abil.get('tick',1))
        target.add_effect(e); out.append(f"You afflict {target.name} with {abil['name']}.")
    elif typ=='hot':
        e=Effect(abil['name'],'hot',amount=abil.get('per_tick',5),duration=abil.get('duration',10),tick=abil.get('tick',1))
        target.add_effect(e); out.append(f"You bless {target.name} with {abil['name']}.")
    elif typ=='buff':
        amt=abil.get('amount',5); dur=abil.get('duration',10)
        mod = dict(abil.get('mod') or {})
        if not mod:
            mod = {'power': amt}
        e=Effect(abil['name'],'buff',duration=dur,mod=mod); p.add_effect(e)
        mod_str = ", ".join(f"{k}+{v}" for k,v in mod.items())
        out.append(f"You empower yourself with {abil['name']} ({mod_str}) for {dur}s.")
    elif typ=='shield':
        val=abil.get('amount',50); target.shield+=val; out.append(f"A shield of {val} surrounds {target.name}.")
    elif typ=='heal':
        heal=abil.get('amount',30) + (p.stats['INT']//3)
        healed=clamp(heal,0,target.max_hp-target.hp); target.hp+=healed
        out.append(f"You heal {target.name} for {healed} HP.")
    elif typ=='lifesteal':
        dmg=abil.get('amount',20) + (p.stats['INT']//4)
        absorbed=target.apply_damage(dmg); leeched=max(0,dmg-absorbed)
        p.hp = clamp(p.hp+leeched, 0, p.max_hp)
        out.append(f"You drain {leeched} life from {target.name} with {abil['name']}.")

    if abil.get('cd'): p.cooldowns[abil['id']]=int(abil['cd'])
    say_room(p.room, '* ' + " ".join(out) + "\n")

async def cmd_attack(p: Player, args):
    if not args:
        await send(p.ws, "Attack what?\n"); return
    name=args[0].lower()
    for m in ROOM_INSTANCES.get(p.room,{}).get('mobs',[]):
        if m.alive and m.name.lower().startswith(name):
            p.target=m.name
            dmg=max(0, (p.power + p.stats['STR']//5) - m.defense)
            absorbed=m.apply_damage(dmg)
            say_room(p.room, f"* {p.name} hits {m.name} for {dmg} ({absorbed} absorbed).\n")
            if not m.alive:
                await mob_death(m, p)
            return
    await send(p.ws, "No such mob here.\n")

# ----------- AUTO-ATTACK ('kill') -----------
def _pick_best_target_for_kill(p: Player):
    inst = ROOM_INSTANCES.get(p.room, {})
    mobs = [m for m in inst.get('mobs',[]) if m.alive]
    if not mobs:
        return None
    # Prefer aggressive mobs first, else any
    aggro = [m for m in mobs if m.aggro]
    return (aggro or mobs)[0]

async def _auto_attack_loop(p: Player):
    try:
        while True:
            await asyncio.sleep(PLAYER_AUTO_SWING)
            if not p.alive: break
            # verify target still valid/alive/in room
            inst = ROOM_INSTANCES.get(p.room, {})
            target = None
            for m in inst.get('mobs', []):
                if m.alive and p.target and m.name.lower().startswith(p.target.lower()):
                    target = m; break
            if not target:
                await send(p.ws, "Your target is gone.\n"); break
            # swing
            dmg = max(0, (p.power + p.stats['STR']//5) - target.defense)
            absorbed = target.apply_damage(dmg)
            say_room(p.room, f"* {p.name} hits {target.name} for {dmg} ({absorbed} absorbed).\n")
            if not target.alive:
                await mob_death(target, p)
                break
    except asyncio.CancelledError:
        return

async def cmd_kill(p: Player, args):
    # choose target if none provided
    target_name = " ".join(args) if args else None
    target_obj = None
    inst = ROOM_INSTANCES.get(p.room, {})
    if target_name:
        for m in inst.get('mobs', []):
            if m.alive and m.name.lower().startswith(target_name.lower()):
                target_obj = m; break
    else:
        target_obj = _pick_best_target_for_kill(p)
    if not target_obj:
        await send(p.ws, "No enemies here.\n"); return
    p.target = target_obj.name
    await send(p.ws, f"You engage {target_obj.name}.\n")

    # one immediate swing to start combat
    dmg=max(0, (p.power + p.stats['STR']//5) - target_obj.defense)
    absorbed=target_obj.apply_damage(dmg)
    say_room(p.room, f"* {p.name} hits {target_obj.name} for {dmg} ({absorbed} absorbed).\n")
    if not target_obj.alive:
        await mob_death(target_obj, p)
        return

    # start/restart auto-loop
    if p._auto_task and not p._auto_task.done():
        p._auto_task.cancel()
        try:
            await p._auto_task
        except asyncio.CancelledError:
            pass
    p._auto_task = asyncio.create_task(_auto_attack_loop(p))

# --------------- NPCs / Quests ---------------
def npcs_in_room(rid):
    return [n for n in NPCS.values() if n.get('room')==rid]

async def cmd_talk(p: Player, args):
    if not args:
        beings=npcs_in_room(p.room)
        if not beings:
            await send(p.ws, "No one to talk to.\n"); return
        await send(p.ws, "You can talk to: "+", ".join(b['name'] for b in beings)+"\n"); return
    whom=args[0].lower()
    for b in npcs_in_room(p.room):
        if b['name'].lower().startswith(whom):
            await send(p.ws, wrap(b.get('greet','They say nothing.'))+"\n")
            # Tegyrios quest chain
            if p.quest and p.quest['id']=='intro_cult_talisman':
                st=p.quest.get('stage',0)
                if st==0:
                    await send(p.ws, wrap(b.get('quest_start','Seek the truth near the Forgotten Acacia.'))+"\n")
                    p.quest['stage']=1; save_player(p)
                elif st==2:
                    if 'Cult Talisman' in p.inventory:
                        await send(p.ws, wrap(b.get('quest_turnin','You found it! We must be vigilant.'))+"\n")
                        p.inventory.remove('Cult Talisman'); p.xp+=50; p.quest=None; save_player(p)
                    else:
                        await send(p.ws, "You don't have the talisman yet.\n")
            # Nihorath simple hunt quest
            if b['name'] == 'Nihorath the Just':
                if not p.quest:
                    p.quest = {'id':'hunt_in_the_woods','stage':0}
                    await send(p.ws, "Nihorath says: 'Hunt a Moonwolf in Nefo'Akhal and return to me.'\n")
                    save_player(p)
                elif p.quest.get('id') == 'hunt_in_the_woods':
                    await send(p.ws, "Nihorath says: 'Your courage steadies others. The hunters thank you.'\n")
                    p.xp += 40
                    p.quest = None
                    save_player(p)
            return
    await send(p.ws, "They aren't here.\n")

async def cmd_search(p: Player):
    if p.room=='forgotten_acacia' and p.quest and p.quest['id']=='intro_cult_talisman' and p.quest.get('stage')==1:
        if 'Cult Talisman' not in p.inventory:
            p.inventory.append('Cult Talisman'); p.quest['stage']=2; save_player(p)
            say_room(p.room, f"* {p.name} finds a strange talisman with two red eyes on two wings.\n")
            return
    await send(p.ws, "You search around but find nothing of note.\n")

# --------------- loot / death ---------------
def rng_chance(pct):
    return random.randint(1,100) <= pct

async def mob_death(m: Mob, killer: Player|None):
    say_room(m.room, f"* {m.name} dies.\n")
    # XP & drops
    if killer:
        killer.xp += 10
        # luck improves drop chance and obols
        luck = killer.stats.get('LCK',10)
        # base drops from template
        drops = []
        for d in (m.loot or []):
            item_name = d.get('item')
            chance = d.get('chance', 25) + luck//5
            if rng_chance(chance):
                drops.append(item_name)
        # small obols coin drop
        obols = 0
        if rng_chance(50 + luck//4):
            obols = random.randint(1,3) + luck//10
            killer.obols += obols
        if drops:
            ground = room_ground(m.room)
            ground.extend(drops)
            say_room(m.room, f"* Loot drops on the ground: {', '.join(drops)}\n")
        if obols:
            await send(killer.ws, f"You loot {obols} Obol(s).\n")
        save_player(killer)

# --------------- MOB TAUNTS ---------------
MOB_TAUNTS = {
    "attack": [
        "{me}: *snarl*",
        "{me}: You'll feed the crows, {you}!",
        "{me}: Pathetic swing!",
        "{me}: Kneel!",
        "{me}: Your bones will sing!",
    ],
    "low_hp": [
        "{me}: I still... stand...",
        "{me}: Is that all you have?",
    ],
    "kill": [
        "{me}: Another one falls!",
        "{me}: The hunt continues.",
    ],
    "spawn": [
        "{me}: *prowls into view*",
    ]
}

def mob_taunt(m: Mob, kind: str, target: Player|None=None, chance: int=30):
    try:
        if random.randint(1,100) > max(0,min(100,chance)):
            return
        lines = MOB_TAUNTS.get(kind) or []
        if not lines:
            return
        tmpl = random.choice(lines)
        text = tmpl.format(me=m.name, you=(target.name if target else "prey"))
        say_room(m.room, f"* {text}\n")
    except Exception:
        pass

# --------------- spawns ---------------
def init_spawns():
    rooms = WORLD.get('rooms') or {}
    for rid, r in rooms.items():
        sp = r.get('spawns', [])
        if sp:
            inst = ROOM_INSTANCES.setdefault(rid, {"mobs": [], "dead_at": {}})
            for t in sp:
                mob = Mob(t, rid)
                inst['mobs'].append(mob)
                mob_taunt(mob, "spawn", chance=25)

def ai_pick_skill(m: Mob):
    ready=[s for s in m.skills if m._skill_cd.get(s['name'].lower(),0)<=0]
    if not ready:
        return None
    return random.choice(ready)

async def mob_ai_attack(m: Mob, targets):
    if not targets: return
    tgt=random.choice(targets)
    acted = False
    # try skill
    skill=ai_pick_skill(m)
    if skill:
        sname=skill['name']; typ=skill.get('type')
        if typ=='damage':
            if isinstance(tgt, Player):
                res = try_dodge_block(tgt)
                if res == "dodge":
                    await send(tgt.ws, f"The {m.name}'s {sname} misses you (dodged).\n")
                    acted = True
                elif res == "block":
                    await send(tgt.ws, f"You block the {m.name}'s {sname}.\n")
                    acted = True
                else:
                    dmg=max(0, m.power + skill.get('amount',6) - tgt.defense)
                    absorbed=tgt.apply_damage(dmg)
                    say_room(m.room, f"* {m.name} uses {sname} on {tgt.name} for {dmg} ({absorbed} absorbed).\n")
                    acted = True
        elif typ=='dot':
            e=Effect(sname,'dot',amount=skill.get('per_tick',4),duration=skill.get('duration',6),tick=1)
            tgt.add_effect(e)
            say_room(m.room, f"* {m.name} afflicts {tgt.name} with {sname}.\n")
            acted = True
        elif typ=='hot':
            e=Effect(sname,'hot',amount=skill.get('per_tick',4),duration=skill.get('duration',6),tick=1)
            m.add_effect(e)
            say_room(m.room, f"* {m.name} mends itself with {sname}.\n")
            acted = True
        if acted:
            cd=int(skill.get('cd',6))
            m._skill_cd[sname.lower()]=cd
            m.flag_combat()
            if isinstance(tgt, Player): tgt.flag_combat()
            if not tgt.alive and isinstance(tgt, Player):
                say_room(m.room, f"* {tgt.name} falls!\n")
                mob_taunt(m, 'kill', target=tgt, chance=70)
            else:
                mob_taunt(m, 'attack', target=tgt, chance=40)
            return

    # basic attack
    if isinstance(tgt, Player):
        res = try_dodge_block(tgt)
        if res == "block":
            await send(tgt.ws, f"You block the {m.name}'s strike.\n")
            m.flag_combat(); tgt.flag_combat()
            return
        if res == "dodge":
            await send(tgt.ws, f"You dodge the {m.name}'s strike.\n")
            m.flag_combat(); tgt.flag_combat()
            return
    dmg=max(0, m.power - tgt.defense)
    absorbed=tgt.apply_damage(dmg)
    say_room(m.room, f"* {m.name} hits {tgt.name} for {dmg} ({absorbed} absorbed).\n")
    m.flag_combat()
    if isinstance(tgt, Player): tgt.flag_combat()
    mob_taunt(m, 'attack', target=tgt, chance=30)
    if not tgt.alive:
        say_room(m.room, f"* {tgt.name} falls!\n")
        mob_taunt(m, 'kill', target=tgt, chance=70)

# --------------- effect ticking & respawn ---------------
async def _tick_effects_on_entity(ent: Entity, send_line_fn):
    remove=[]
    for eff in list(ent.effects):
        eff.remaining -= 1
        eff.next_tick_in -= 1
        if eff.next_tick_in <= 0:
            for line in eff.on_tick(ent):
                await send_line_fn(line)
        if eff.remaining <= 0:
            remove.append(eff)
    for e in remove:
        # undo temporary mods (e.g., buffs)
        if e.mod:
            ent.remove_mods(e.mod)
        ent.effects.remove(e)

async def _maybe_respawn_player(p: Player):
    if p.alive:
        p._dead_since = None
        return
    if p._dead_since is None:
        p._dead_since = time.time()
        return
    if time.time() - p._dead_since >= DEATH_RESPAWN_SECONDS:
        p.alive = True
        p.room = 'trade_district'
        p.hp = max(1, p.max_hp // 2)
        p._dead_since = None
        await send(p.ws, "You awaken at the Trade District.\n")
        await show_room(p)
        save_player(p)

# --------------- heartbeat (pacing + lifecycle safe) ---------------
async def heartbeat():
    try:
        while True:
            await asyncio.sleep(TICK_SECONDS)
            # player cooldowns & effects & combat decay & respawn
            for p in list(PLAYERS.values()):
                # cooldowns
                for k in list(p.cooldowns.keys()):
                    p.cooldowns[k]=max(0, p.cooldowns[k]-1)
                    if p.cooldowns[k]<=0: del p.cooldowns[k]
                # effects
                async def _p_send(line):
                    await send(p.ws, line+"\n")
                await _tick_effects_on_entity(p, _p_send)
                # death/respawn
                await _maybe_respawn_player(p)

            # mobs AI & cooldowns/effects
            for rid, inst in ROOM_INSTANCES.items():
                for m in list(inst.get('mobs',[])):
                    try:
                        # dead/respawn
                        if not m.alive:
                            inst.setdefault('dead_at',{})
                            if m not in inst['dead_at']:
                                inst['dead_at'][m]=time.time()
                            elif time.time()-inst['dead_at'][m]>=m.respawn:
                                inst['mobs'].remove(m)
                                newm=Mob(m.template_id,rid)
                                inst['mobs'].append(newm)
                                inst['dead_at'].pop(m,None)
                                say_room(rid, f"* A {newm.name} prowls in from the wilds.\n")
                                mob_taunt(newm, 'spawn', chance=25)
                            continue

                        # reduce skill cooldowns
                        for sk,cd in list(m._skill_cd.items()):
                            m._skill_cd[sk]=max(0, cd-1)
                            if m._skill_cd[sk]<=0: m._skill_cd.pop(sk,None)

                        # ticking effects on mob
                        async def _m_say(line):
                            say_room(rid, f"* {line}\n")
                        await _tick_effects_on_entity(m, _m_say)

                        # AI pacing
                        m._ai_cd = max(0, m._ai_cd - TICK_SECONDS)

                        # aggro AI (attack if aggressive OR recently put in combat by being hit)
                        if (m.aggro or m.in_combat) and m._ai_cd <= 0:
                            candidates=[p for p in PLAYERS.values() if p.room==rid and p.alive]
                            if candidates:
                                await mob_ai_attack(m, candidates)
                            # reset AI cd with slight jitter
                            m._ai_cd = MOB_AI_PERIOD + random.uniform(-MOB_AI_JITTER, MOB_AI_JITTER)

                        # low hp taunt
                        if m.alive and m.hp <= max(5, m.max_hp//4) and rng_chance(10):
                            mob_taunt(m, "low_hp", chance=60)
                    except Exception as e:
                        print(f"[Heartbeat AI error for {m.name} in {rid}]", e)
    except asyncio.CancelledError:
        return

# lifecycle hooks to manage heartbeat task
async def start_background_tasks(app):
    app['heartbeat_task'] = asyncio.create_task(heartbeat())

async def cleanup_background_tasks(app):
    task = app.get('heartbeat_task')
    if task:
        task.cancel()
        try:
            await task
        except asyncio.CancelledError:
            pass

# --------------- ECONOMY / SHOP / LOOTING ---------------
def is_shop_room(rid):
    for sid, s in (SHOPS.get('shops') or {}).items():
        if s.get('room')==rid:
            return sid
    return None

def value_of_item(name):
    d=get_item_def(name)
    if not d: return 0
    return int(d.get('value', d.get('vendor_value', 0)))

async def cmd_shop(p: Player):
    sid=is_shop_room(p.room)
    if not sid:
        await send(p.ws, "There is no shop here.\n"); return
    s=SHOPS['shops'][sid]
    lines=[f"{s.get('name','Shop')} — You have {p.obols} Obols."]
    for item,entry in (s.get('inventory') or {}).items():
        price = entry.get('price', 1)
        lines.append(f"- {item} : {price} Obols")
    await send(p.ws, "\n".join(lines)+"\n")

async def cmd_buy(p: Player, args):
    if not args:
        await send(p.ws,"Buy what?\n"); return
    sid=is_shop_room(p.room)
    if not sid:
        await send(p.ws, "There is no shop here.\n"); return
    s=SHOPS['shops'][sid]
    want=" ".join(args)
    sel=None
    for item in s.get('inventory',{}).keys():
        if norm(item)==norm(want) or norm(item).startswith(norm(want)):
            sel=item; break
    if not sel:
        await send(p.ws,"They don't sell that.\n"); return
    price=int(s['inventory'][sel].get('price',1))
    if p.obols < price:
        await send(p.ws, "You don't have enough Obols.\n"); return
    p.obols -= price
    p.inventory.append(sel)
    await send(p.ws, f"You buy {sel} for {price} Obols.\n")
    save_player(p)

async def cmd_sell(p: Player, args):
    if not args:
        await send(p.ws, "Sell what?\n"); return
    sid=is_shop_room(p.room)
    if not sid:
        await send(p.ws, "There is no shop here.\n"); return
    want=" ".join(args)
    inv_match=None
    for it in p.inventory:
        if norm(it)==norm(want) or norm(it).startswith(norm(want)):
            inv_match=it; break
    if not inv_match:
        await send(p.ws, "You don't have that.\n"); return
    val=max(1, value_of_item(inv_match))
    p.inventory.remove(inv_match)
    p.obols += val
    await send(p.ws, f"You sell {inv_match} for {val} Obols. You now have {p.obols}.\n")
    save_player(p)

async def cmd_get(p: Player, args):
    if not args:
        await send(p.ws,"Get what?\n"); return
    want=" ".join(args)
    ground=room_ground(p.room)
    pick=None
    for g in ground:
        if norm(g)==norm(want) or norm(g).startswith(norm(want)):
            pick=g; break
    if not pick:
        await send(p.ws,"You don't see that here.\n"); return
    ground.remove(pick)
    p.inventory.append(pick)
    await send(p.ws, f"You pick up {pick}.\n")
    save_player(p)

async def cmd_drop(p: Player, args):
    if not args:
        await send(p.ws,"Drop what?\n"); return
    want=" ".join(args)
    inv_match=None
    for it in p.inventory:
        if norm(it)==norm(want) or norm(it).startswith(norm(want)):
            inv_match=it; break
    if not inv_match:
        await send(p.ws, "You don't have that.\n"); return
    p.inventory.remove(inv_match)
    room_ground(p.room).append(inv_match)
    say_room(p.room, f"* {p.name} drops {inv_match}.\n")
    save_player(p)

# --------------- EQUIPMENT & INFO ---------------
async def cmd_equip(p: Player, args):
    if not args:
        await send(p.ws,"Equip what?\n"); return
    want=" ".join(args)
    inv_match=None
    for it in p.inventory:
        if norm(it)==norm(want) or norm(it).startswith(norm(want)):
            inv_match=it; break
    if not inv_match:
        await send(p.ws,"You don't have that.\n"); return
    idef=get_item_def(inv_match)
    typ=idef.get('type')
    if typ=='weapon':
        p.equipment['weapon']=inv_match
    elif typ=='armor_set':
        p.equipment['set']=inv_match
    elif typ=='shield':
        p.equipment['shield']=inv_match
    else:
        await send(p.ws,"You can't equip that.\n"); return
    p.recompute_stats()
    await send(p.ws, f"You equip {inv_match}.\n")
    save_player(p)

async def cmd_unequip(p: Player, args):
    if not args:
        await send(p.ws,"Unequip what? (weapon|set|shield)\n"); return
    slot=args[0].lower()
    if not p.equipment.get(slot):
        await send(p.ws,"Nothing equipped there.\n"); return
    item=p.equipment[slot]
    p.equipment[slot]=None
    p.recompute_stats()
    await send(p.ws, f"You unequip {item}.\n")
    save_player(p)

async def cmd_gear(p: Player):
    eq=p.equipment
    await send(p.ws, f"Gear — Weapon: {eq.get('weapon') or '(none)'} | Shield: {eq.get('shield') or '(none)'} | Set: {eq.get('set') or '(none)'}\n")

async def cmd_examine(p: Player, args):
    if not args:
        await send(p.ws,"Examine what?\n"); return
    want=" ".join(args)
    target=None
    for it in p.inventory:
        if norm(it)==norm(want) or norm(it).startswith(norm(want)):
            target=it; break
    if not target:
        target=match_item_name(want)
    if not target:
        await send(p.ws, "You don't see that item.\n"); return
    d=get_item_def(target)
    if not d:
        await send(p.ws,"Unknown item.\n"); return
    lines=[f"{target} — {d.get('type','item')}"]
    if d.get('desc'): lines.append(d['desc'])
    if d.get('mods'):
        modparts=[f"{k}+{v}" for k,v in d['mods'].items()]
        lines.append("Stats: " + ", ".join(modparts))
    val=value_of_item(target)
    lines.append(f"Vendor value: {val} Obols")
    await send(p.ws, "\n".join(lines)+"\n")

# --------------- REST (background) ---------------
async def do_rest(p: Player):
    try:
        for i in range(6):
            await asyncio.sleep(10)
            if p.in_combat or not p.alive:
                await send(p.ws, "You were disturbed and stop resting.\n")
                return
            p.hp = clamp(p.hp + (p.max_hp//6), 0, p.max_hp)
            await send(p.ws, f"Resting... HP {p.hp}/{p.max_hp}\n")
        await send(p.ws, "You finish resting.\n")
    finally:
        p._rest_task=None

# --------------- command handling ---------------
async def handle_command(p: Player, line: str):
    verb, args = normalize_cmd(line)
    if not verb:
        return

    if verb in ('help','h'):
        await send(p.ws, wrap("Commands: look, go <dir>, n/s/e/w/ne/nw/se/sw/u/d, say <msg>, who, stats, abilities, use <ability> [target], target <name>, attack <mob>, kill [mob], talk [npc], quest, search, inventory|inv, get <item>, drop <item>, shop, buy <item>, sell <item>, gear, equip <item>, unequip <slot>, examine <item>, recall, rest, quit")+"\n")
    elif verb in ('look','l'):
        await show_room(p)
    elif verb=='go':
        if not args:
            await send(p.ws, "Go where?\n"); return
        direc=args[0]
        r = room(p.room) or {}
        dest=(r.get('exits') or {}).get(direc)
        if not dest:
            await send(p.ws, "You can't go that way.\n"); return
        if p.in_combat:
            await send(p.ws, "You can't flee while in combat!\n"); return
        # cancel auto attack if moving
        if p._auto_task and not p._auto_task.done():
            p._auto_task.cancel()
            try:
                await p._auto_task
            except asyncio.CancelledError:
                pass
            p._auto_task=None
        say_room(p.room, f"* {p.name} leaves {direc}.\n", exclude=p.ws)
        p.room=dest
        say_room(p.room, f"* {p.name} arrives.\n", exclude=p.ws)
        save_player(p)
        await show_room(p)
    elif verb=='say':
        if args:
            say_room(p.room, f"{p.name} says: {' '.join(args)}\n")
    elif verb=='who':
        names=[q.name for q in PLAYERS.values() if q.name]
        await send(p.ws, f"Players ({len(names)}): "+", ".join(names)+"\n")
    elif verb=='stats':
        st=p.stats
        await send(p.ws, f"{p.name} — {p.race} {p.cls} ({p.archetype}), {p.deity}\nHP {p.hp}/{p.max_hp} | Pow {p.power} | Def {p.defense} | Obols {p.obols}\nSTR {st['STR']} | INT {st['INT']} | DEX {st['DEX']} | DEF {st['DEF']} | LCK {st['LCK']}\n")
    elif verb=='abilities':
        for a in ability_defs_for(p):
            cd=p.cooldowns.get(a.get('id',''),0)
            await send(p.ws, f"- {a.get('name','(unknown)')} ({a.get('id','?')}) {('[CD:'+str(cd)+'s]') if cd else ''}\n")
    elif verb=='use':
        await cmd_use(p, args)
    elif verb=='target':
        if args:
            p.target=" ".join(args); await send(p.ws, f"Target set to {p.target}.\n")
        else:
            await send(p.ws, f"Current target: {p.target or 'none'}\n")
    elif verb=='attack':
        await cmd_attack(p, args)
    elif verb=='kill':
        await cmd_kill(p, args)
    elif verb=='talk':
        await cmd_talk(p, args)
    elif verb=='quest':
        await send(p.ws, json.dumps(p.quest, indent=2)+"\n")
    elif verb=='search':
        await cmd_search(p)
    elif verb in ('inventory','inv'):
        inv = ", ".join(p.inventory) if p.inventory else "(empty)"
        await send(p.ws, f"Inventory: {inv}\n")
    elif verb=='get':
        await cmd_get(p, args)
    elif verb=='drop':
        await cmd_drop(p, args)
    elif verb=='shop':
        await cmd_shop(p)
    elif verb=='buy':
        await cmd_buy(p, args)
    elif verb=='sell':
        await cmd_sell(p, args)
    elif verb=='gear':
        await cmd_gear(p)
    elif verb=='equip':
        await cmd_equip(p, args)
    elif verb=='unequip':
        await cmd_unequip(p, args)
    elif verb=='examine':
        await cmd_examine(p, args)
    elif verb=='recall':
        if p.in_combat:
            await send(p.ws, "You cannot recall during combat!\n"); return
        # cancel auto attack if recalling
        if p._auto_task and not p._auto_task.done():
            p._auto_task.cancel()
            try:
                await p._auto_task
            except asyncio.CancelledError:
                pass
            p._auto_task=None
        old = p.room
        p.room='trade_district'
        say_room(old, f"* {p.name} vanishes in a swirl of light.\n", exclude=p.ws)
        say_room(p.room, f"* {p.name} appears in a swirl of light.\n", exclude=p.ws)
        save_player(p)
        await show_room(p)
    elif verb=='rest':
        if p.in_combat:
            await send(p.ws, "You cannot rest during combat!\n"); return
        if p._rest_task and not p._rest_task.done():
            await send(p.ws, "You are already resting.\n"); return
        await send(p.ws, "You begin to rest...\n")
        p._rest_task = asyncio.create_task(do_rest(p))
    elif verb=='quit':
        await send(p.ws, "Goodbye.\n")
        # cancel auto attack if quitting
        if p._auto_task and not p._auto_task.done():
            p._auto_task.cancel()
            try:
                await p._auto_task
            except asyncio.CancelledError:
                pass
            p._auto_task=None
        await p.ws.close()
    else:
        await send(p.ws, "Unknown command. Try 'help'.\n")

# --------------- websocket + web app ---------------
async def ws_handler(request):
    ws = web.WebSocketResponse()
    await ws.prepare(request)

    ip = request.remote
    p = Player(ws, ip)
    PLAYERS[ws] = p

    await send(ws, "=== NEKHIA (web alpha) ===\n")
    ok = await create_character(p)
    if not ok:
        await ws.close(); PLAYERS.pop(ws, None); return ws

    try:
        async for msg in ws:
            if msg.type == web.WSMsgType.TEXT:
                await handle_command(p, msg.data)
            else:
                break
    finally:
        try:
            if p.name:
                save_player(p)
        except Exception as e:
            print("Save on disconnect failed:", e)
        PLAYERS.pop(ws, None)
        try:
            await ws.close()
        except Exception:
            pass
    return ws

async def index(request):
    return web.FileResponse((ROOT/"static"/"index.html").as_posix())

app = web.Application()
app.add_routes([
    web.get('/', index),
    web.get('/ws', ws_handler),
    web.static('/static', (ROOT/"static").as_posix()),
])

# tie heartbeat to app lifecycle
app.on_startup.append(start_background_tasks)
app.on_cleanup.append(cleanup_background_tasks)

# init spawns (heartbeat starts via startup hook)
init_spawns()

if __name__ == '__main__':
    PORT = int(os.getenv('PORT', '8080'))
    web.run_app(app, host='0.0.0.0', port=PORT)
