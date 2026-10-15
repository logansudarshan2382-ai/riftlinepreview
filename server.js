'use strict';
/*
 * Riftline game server (Step 7): modes, weapons, three maps (one a floating space station), a drivable vehicle, player progression,
 * a spawn-point matrix and out-of-bounds / kill-zone deaths.
 *
 * Environment variables (all optional):
 *   MODE       tdm | ffa            lock one game mode (default: alternate every match)
 *   MAP        field | arena | station   lock one map (default: rotate through all of them)
 *   ADMIN_KEY  any secret text      turns on /admin so you can load a map or mode on the spot (see below)
 *   TDM_LIMIT, FFA_LIMIT            kills needed to win
 *   ALLOWED_ORIGINS                 your website address(es), comma separated
 *   SAVE_SECRET  any long secret    signs each player's backup save. SET THIS: Render's free plan wipes files on every restart,
 *                                   and the signed backup (kept in the player's browser) is what restores their progress
 *   DATA_DIR                        where profiles.json lives (default ./data; only survives restarts on a paid host with a disk)
 *
 * Host controls, once ADMIN_KEY is set (open these in a browser; keep the key secret):
 *   https://YOUR-SERVER/admin?key=KEY&map=arena            load a map and restart the match
 *   https://YOUR-SERVER/admin?key=KEY&map=field&mode=ffa   load a map and a mode
 *   https://YOUR-SERVER/admin?key=KEY                      show what is running
 *
 * client -> server   state {e,x,y,z,yaw,pitch}  shoot {ox,oy,oz,dx,dy,dz}  reload  switch i  name 'text'
 *                    use (the E key: get in or out of a vehicle)   veh {x,z,yaw,speed} (the driver's vehicle pose)
 * server -> client   welcome, join, leave, rename, factions, match, map      who is here, what is being played, where
 *                    snapshot [[id,x,y,z,yaw,pitch,alive,vehicleId]]          where every player is, 20x/s
 *                    vehicles [[id,x,z,yaw,driverId]]   drive / undrive      vehicle poses and who is driving
 *                    you {hp,ammos,wi,reloading}  hit  fx  kill  scores  respawn {x,y,z,yaw,...}
 *                    kill {k:0, why} is a fall or a kill zone: no killer, the reason goes in the kill feed
 *                    profile {xp,level,into,need,coins,owned,eq,save,gain?}   your progress, after every change
 *                    skin {id,body,weapon}   someone equipped a skin: everyone repaints them     notice {text}
 * client -> server   (also) buy 'skinId'   equip 'skinId'    and on connect: auth {token, save}
 *
 * The server decides every hit, kill and point, and owns the weapon and map tables (clients just follow them).
 * Player and vehicle positions are still reported by the client and only sanity-checked.
 */
const express = require('express');
const http = require('http');
const path = require('path');
const crypto = require('crypto');
const fs = require('fs');
const { Server } = require('socket.io');

const PORT = process.env.PORT || 3000;
// The arcade site lives on a different host than this server, so list its address(es) here.
// Any http://localhost:<port> is always allowed for local testing.
const ORIGINS = (process.env.ALLOWED_ORIGINS || 'https://fungames-arcade.netlify.app').split(',').map(s => s.trim());
const MODE = ['tdm', 'ffa'].includes(process.env.MODE) ? process.env.MODE : 'rotate';
const TICK_HZ = 20, MAX_PLAYERS = 16;
const REGION = (process.env.REGION || 'US').toUpperCase().replace(/[^A-Z]/g, '').slice(0, 4) || 'US', MAX_ROOMS = Number(process.env.MAX_ROOMS) || 50, ROOM_IDLE_MS = 60000;   // REGION names the rooms (Server-EU-2); MAX_ROOMS caps one process
const HP = 100, RESPAWN_MS = 3000, INTERMISSION_MS = 8000, SWITCH_MS = 350;
const LIMIT = { tdm: Number(process.env.TDM_LIMIT) || 20, ffa: Number(process.env.FFA_LIMIT) || 10 };   // kills needed to win
const BODY = { r: .4, h: 1.8, eye: 1.62 };
const VEH = { hx: 1.3, hz: 2.5, h: 1.6, maxSpeed: 22, maxReverse: 6, useRange: 1.8 };
const VTYPES = {   // vehicle classes: footprint, height and speed limits (m/s). A ground car is fast and runs people over; the helicopter flies; the mech walks.
  car:  { hx: 1.3, hz: 2.5, h: 1.6, maxSpeed: 22, maxReverse: 6 },
  heli: { hx: 1.5, hz: 3.4, h: 2.6, maxSpeed: 20, maxReverse: 20 },
  mech: { hx: 1.5, hz: 1.5, h: 5.6, maxSpeed: 4.5, maxReverse: 4.5 },
  tank: { hx: 1.7, hz: 3.0, h: 2.2, maxSpeed: 9, maxReverse: 4 },   // slow, heavy, crushes people it drives over, and fires a shell
  turret: { hx: 1.4, hz: 1.4, h: 1, maxSpeed: 0, maxReverse: 0 }    // a manned gun nest on top of a pillar: it never moves, the footprint is where you climb out
};
const vd = v => VTYPES[v.type] || VTYPES.car;
const VWEAPONS = {   // what a driver's left click fires. Helicopter rockets are slow; the mech's miniguns heat up (+2.2 a shot, cooling 18 a second, locked for 2.5 s at 100)
  heli: { damage: 100, headshotMultiplier: 1, fireRateDelay: 1400, range: 300, splash: { radius: 8, damage: 90 } },
  mech: { damage: 5, headshotMultiplier: 1, fireRateDelay: 45, range: 120, heat: 2.2 },
  tank: { damage: 100, headshotMultiplier: 1, fireRateDelay: 1600, range: 300, splash: { radius: 7, damage: 90 } },
  turret: { damage: 14, headshotMultiplier: 1.5, fireRateDelay: 90, range: 150 },   // a pillar-top gun
  cargun: { damage: 9, headshotMultiplier: 1.3, fireRateDelay: 75, range: 110 }      // the roof gun of a car, fired by a passenger
};
const TURRET = { radius: 80, damage: 6, headshotMultiplier: 1, fireRateDelay: 110, range: 80 };   // base turrets: the radius is their scanner dome

// ---- progression: XP, levels, coins and skins, saved per player ----
const XP_PER_KILL = 100, COINS_PER_KILL = 10, WIN_COINS = 50, LEVEL_UP_COINS = 25, MAX_PROFILES = 5000;
const xpToNext = level => 200 + 100 * level;   // level 1 -> 2 takes 300 XP, then 400, 500 ...
function levelInfo(xp) { let level = 1, rest = xp; while (rest >= xpToNext(level)) { rest -= xpToNext(level); level++; } return { level, into: rest, need: xpToNext(level) }; }

// Cosmetics only. Body skins repaint the capsule, but the faction colour still glows through so teams stay readable.
// Weapon skins repaint the gun and can recolour its tracer. color: null means "use the faction colour".
const SKINS = [
  { id: 'issue',    slot: 'body',   name: 'Faction issue',   price: 0,    level: 1, color: null,     metal: .25, rough: .45, glow: .3 },
  // premium finishes: fx picks the material preset on the client (carbon = woven bump map, chrome = mirror with glowing stripes, camo = see-through refraction)
  { id: 'carbon',   slot: 'body',   name: 'Carbon Fiber',    price: 500,  level: 1, color: 0x70757f, metal: .6,  rough: .35, glow: .4,  fx: 'carbon' },
  { id: 'chrome',   slot: 'body',   name: 'Neon Chrome',     price: 1200, level: 3, color: 0xdff3ff, metal: 1,   rough: .12, glow: 1.1, fx: 'chrome' },
  { id: 'camo',     slot: 'body',   name: 'Active Camouflage',     price: 2500, level: 6, color: 0xb9d8e6, metal: .2,  rough: .1,  glow: .12, fx: 'camo' },
  { id: 'ember',    slot: 'body',   name: 'Ember',           price: 1200, level: 5, color: 0x8a2a0a, metal: .5,  rough: .4,  glow: .6 },
  { id: 'void',     slot: 'body',   name: 'Void Glass',      price: 2000, level: 8, color: 0x2a1a55, metal: .9,  rough: .1,  glow: .55 },
  { id: 'w-issue',  slot: 'weapon', name: 'Standard finish', price: 0,    level: 1, color: 0x3a3f4d, metal: .6,  rough: .45, beam: null },
  { id: 'w-carbon', slot: 'weapon', name: 'Carbon',          price: 250,  level: 1, color: 0x15161a, metal: .7,  rough: .35, beam: null },
  { id: 'w-chrome', slot: 'weapon', name: 'Neon Chrome',     price: 700,  level: 3, color: 0xdff3ff, metal: 1,   rough: .12, beam: 0x9bf5ff },
  { id: 'w-ember',  slot: 'weapon', name: 'Ember',           price: 1000, level: 5, color: 0x8a2a0a, metal: .5,  rough: .4,  beam: 0xff8a3a },
  // ---- Step 15 premium shader skins (fx 'shader': m picks the animated GLSL pattern on the client; the faction colour always layers through it) ----
  { id: 'gold',     slot: 'body', name: 'Gold Leaf',       price: 1500, level: 4,  color: 0xf2b81f, metal: 1,  rough: .25, glow: .15, fx: 'shader', m: 1 },
  { id: 'obsidian', slot: 'body', name: 'Obsidian Glass',  price: 2200, level: 7,  color: 0x05050a, metal: .9, rough: .04, glow: .8,  fx: 'shader', m: 2 },
  { id: 'plasma',   slot: 'body', name: 'Plasma Fire',     price: 2600, level: 9,  color: 0xff6a10, metal: .1, rough: .6,  glow: 1.2, fx: 'shader', m: 3 },
  { id: 'frost',    slot: 'body', name: 'Titanium Frost',  price: 1800, level: 5,  color: 0xc4d8ec, metal: .8, rough: .3,  glow: .3,  fx: 'shader', m: 4 },
  { id: 'rust',     slot: 'body', name: 'Rusty Junkyard',  price: 700,  level: 2,  color: 0x7a4a24, metal: .3, rough: .9,  glow: .1,  fx: 'shader', m: 5 },
  { id: 'punk',     slot: 'body', name: 'Cyber Punk',      price: 2400, level: 8,  color: 0xff2ad4, metal: .6, rough: .3,  glow: 1,   fx: 'shader', m: 6 },
  { id: 'voidm',    slot: 'body', name: 'Void Matter',     price: 3000, level: 12, color: 0x120022, metal: .3, rough: .3,  glow: 1.3, fx: 'shader', m: 7 },
  { id: 'digi',     slot: 'body', name: 'Digital Camo',    price: 900,  level: 3,  color: 0x5a6b45, metal: .2, rough: .8,  glow: .1,  fx: 'shader', m: 8 },
  { id: 'matrix',   slot: 'body', name: 'Matrix Code',     price: 2800, level: 10, color: 0x00ff40, metal: .2, rough: .4,  glow: 1.1, fx: 'shader', m: 9 },
  { id: 'solar',    slot: 'body', name: 'Solar Flare',     price: 3200, level: 13, color: 0xffb020, metal: .1, rough: .5,  glow: 1.5, fx: 'shader', m: 10 },
  { id: 'space',    slot: 'body', name: 'Deep Space',      price: 3500, level: 15, color: 0x0a0a30, metal: .5, rough: .3,  glow: 1,   fx: 'shader', m: 11 },
  { id: 'acid',     slot: 'body', name: 'Acid Spill',      price: 2000, level: 6,  color: 0x99ff1a, metal: .2, rough: .2,  glow: 1,   fx: 'shader', m: 12 },
  // ---- Step 15 exoskeleton frames. hp = armour health, spd/jump = movement multipliers, blast = explosive damage resisted, quiet = silent footsteps,
  //      dash = seconds to recharge the Q dash, melee = multiplier on the F strike ----
  { id: 'f-raider', slot: 'frame', name: 'Vanguard Raider Frame', price: 0,    level: 1, color: 0x9aa3b5, metal: .6, rough: .4, glow: 0, fr: { hp: 100, spd: 1,   jump: 1,    blast: 0,  quiet: 0, dash: 4,   melee: 1.5 } },
  { id: 'f-apex',   slot: 'frame', name: 'Apex Predator Frame',   price: 1500, level: 4, color: 0xff7a2a, metal: .6, rough: .4, glow: 0, fr: { hp: 70,  spd: 1.3, jump: 1.25, blast: 0,  quiet: 0, dash: 4,   melee: 1 } },
  { id: 'f-jugg',   slot: 'frame', name: 'Juggernaut Frame',      price: 2500, level: 8, color: 0x7f8794, metal: .8, rough: .5, glow: 0, fr: { hp: 200, spd: .78, jump: .85,  blast: .6, quiet: 0, dash: 5.5, melee: 1 } },
  { id: 'f-ghost',  slot: 'frame', name: 'Void Ghost Frame',      price: 2000, level: 6, color: 0x6a3fd0, metal: .5, rough: .3, glow: 0, fr: { hp: 100, spd: 1,   jump: 1,    blast: 0,  quiet: 1, dash: 2.2, melee: 1 } }
];
const PREMIUM = ['carbon', 'chrome', 'camo', 'gold', 'obsidian', 'plasma', 'frost', 'rust', 'punk', 'voidm', 'digi', 'matrix', 'solar', 'space', 'acid'];   // the 15 premium skins bots draw from
const skinById = new Map(SKINS.map(s => [s.id, s]));
const newProfile = () => ({ xp: 0, coins: 0, kills: 0, owned: ['issue', 'w-issue', 'f-raider'], eq: { body: 'issue', weapon: 'w-issue', frame: 'f-raider' }, rev: 0, seen: Date.now() });

// The "mock database": every profile in one JSON file, keyed by a secret token that the player's browser keeps.
// Render's free plan wipes local files on every restart or sleep, so each player's browser also holds a signed backup
// (see sign/adopt below). The signature uses SAVE_SECRET, so a player can't edit their own XP or coins.
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const SAVE_SECRET = process.env.SAVE_SECRET || crypto.randomBytes(32).toString('hex');
if (!process.env.SAVE_SECRET) console.warn("SAVE_SECRET is not set: players' backup saves will stop working whenever this server restarts.");
class Store {
  constructor(file) {
    this.file = file; this.timer = null; this.data = {};
    try {
      const d = JSON.parse(fs.readFileSync(file, 'utf8'));
      for (const k of Object.keys(d)) if (/^[a-f0-9]{32}$/.test(k) && d[k] && Array.isArray(d[k].owned) && d[k].eq) { if (d[k].coins == null) { d[k].coins = d[k].credits || 0; delete d[k].credits; } this.data[k] = d[k]; }   // older saves called coins "credits"
    } catch (e) { /* first run, or the host wiped its disk */ }
  }
  get(token) { return Object.prototype.hasOwnProperty.call(this.data, token) ? this.data[token] : undefined; }
  set(token, prof) {
    prof.seen = Date.now(); this.data[token] = prof;
    const keys = Object.keys(this.data);
    if (keys.length > MAX_PROFILES) { keys.sort((a, b) => this.data[a].seen - this.data[b].seen); for (const k of keys.slice(0, keys.length - MAX_PROFILES)) delete this.data[k]; }
    clearTimeout(this.timer); this.timer = setTimeout(() => this.flush(), 2000);   // write a moment later, not on every kill
  }
  flush() {
    try { fs.mkdirSync(path.dirname(this.file), { recursive: true }); fs.writeFileSync(this.file + '.tmp', JSON.stringify(this.data)); fs.renameSync(this.file + '.tmp', this.file); }
    catch (e) { console.warn('could not save profiles:', e.message); }
  }
}
const store = new Store(path.join(DATA_DIR, 'profiles.json'));

const mac = body => crypto.createHmac('sha256', SAVE_SECRET).update(body).digest('base64url');
function sign(token, p) {   // a tamper-proof copy of the profile for the player's browser to keep
  const body = Buffer.from(JSON.stringify({ t: token, xp: p.xp, coins: p.coins, kills: p.kills, owned: p.owned, eq: p.eq })).toString('base64url');
  return body + '.' + mac(body);
}
function adopt(token, save) {   // restore a profile from a signed backup, if the signature is ours and it belongs to this token
  if (typeof save !== 'string' || save.length > 4000) return null;
  const [body, sig] = save.split('.');
  if (!body || !sig || !safeEqual(sig, mac(body))) return null;
  try {
    const d = JSON.parse(Buffer.from(body, 'base64url').toString());
    if (d.t !== token) return null;
    const owned = [...new Set(['issue', 'w-issue', 'f-raider', ...(Array.isArray(d.owned) ? d.owned : []).filter(id => skinById.has(id))])];
    const worn = (id, slot, def) => (owned.includes(id) && skinById.get(id).slot === slot ? id : def);
    const n = v => Math.max(0, Math.floor(Number(v)) || 0);
    return { xp: n(d.xp), coins: n(d.coins != null ? d.coins : d.credits), kills: n(d.kills), owned, eq: { body: worn(d.eq && d.eq.body, 'body', 'issue'), weapon: worn(d.eq && d.eq.weapon, 'weapon', 'w-issue'), frame: worn(d.eq && d.eq.frame, 'frame', 'f-raider') }, rev: 1, seen: Date.now() };
  } catch (e) { return null; }
}

// ---- weapons: the first one is what everybody spawns with. Add a line here and it appears in the game. ----
const WEAPONS = [   // damage per bullet, delay between shots (ms), magazine size, spare ammo (maxAmmo), reload seconds, range in metres, level needed. HP is 100.
  // Per player, currentMagazine is p.ammos[i] and currentAmmo (the spare rounds) is p.reserve[i]. `splash` = explosion radius (m) and damage at its centre.
  { name: 'Assault rifle',   short: 'RIFLE',  damage: 7,   headshotMultiplier: 1.5, fireRateDelay: 70,   magazineSize: 250, maxAmmo: 750, reloadTime: 1.4, range: 60,  unlockLevel: 1,  auto: true,  len: 1 },
  { name: 'Sniper rifle',    short: 'SNIPER', damage: 50,  headshotMultiplier: 2,   fireRateDelay: 450,  magazineSize: 5,   maxAmmo: 20,  reloadTime: 4.5, range: 400, unlockLevel: 5,  auto: false, len: 1.5 },
  { name: 'Rocket launcher', short: 'ROCKET', damage: 100, headshotMultiplier: 1,   fireRateDelay: 1800, magazineSize: 1,   maxAmmo: 6,   reloadTime: 5,   range: 250, unlockLevel: 10, auto: false, len: 1.4, splash: { radius: 7, damage: 90 } }
];

// ---- maps ----
// A map is plain data. The server sends it to every player and each browser builds the scene from it.
//   blocks     solid boxes: x/z centre, hx/hz half-sizes, h height, y bottom (default 0), kind = how it looks
//              (crate, pillar, wall, building, platform, deck, ceiling). You can stand on top, bump your head underneath, never walk through.
//   ramps      walkable slopes: x/z centre, hx/hz half-sizes, y0 = height at the low end, y1 = height at the high end, dir = the way it climbs (N, S, E, W)
//   ground     height of an invisible floor (0), or null when blocks are the only floors, as on a floating arena
//   bounds     the play box [min x,y,z] to [max x,y,z]. edge 'wall': an invisible wall keeps you inside.
//              edge 'void': nothing stops you, and leaving the box (or falling below its floor) is a death
//   killZones  boxes that kill on entry, each with the words for the kill feed
//   spawns     { ffa, vanguard, horizon }: points { x, y, z, yaw }. Free-for-all uses ffa; team deathmatch uses the player's own team list.
//              Keep at least 16 ffa points and 8 per team, 3.5 m apart. validateMap() below checks all of this at startup.
const B = (x, z, hx, hz, h, kind = 'wall', y = 0) => ({ x, z, hx, hz, h, y, kind });
const RAMP = (x, z, hx, hz, y0, y1, dir) => ({ x, z, hx, hz, y0, y1, dir });
const rd = v => Math.round(v * 100) / 100;
const face = (x, z, tx, tz) => rd(Math.atan2(-(tx - x), -(tz - z)));   // the yaw that looks from (x, z) toward (tx, tz); yaw 0 looks along -Z
const at = (x, y, z, look = [0, 0]) => ({ x, y, z, yaw: face(x, z, look[0], look[1]) });
const spawnRow = (x0, z0, x1, z1, n, look = [0, 0], y = 0) => Array.from({ length: n }, (_, i) => { const t = n === 1 ? .5 : i / (n - 1); return at(rd(x0 + (x1 - x0) * t), y, rd(z0 + (z1 - z0) * t), look); });
const spawnRing = (r, n, look = [0, 0]) => Array.from({ length: n }, (_, i) => { const a = i * 2 * Math.PI / n; return at(rd(r * Math.cos(a)), 0, rd(r * Math.sin(a)), look); });

const MAPS = {
  field: {   // open ground, tall pillars, low cover and two bunkers
    id: 'field', name: 'Pillar Fields', half: 60, theme: 'meadow', sky: 0xc2e7ff, fog: [60, 260], sun: true, ceiling: 0, lights: [], tint: 0xe6edf3, accent: 0x7ec8ff, stars: false,
    ground: 0, bounds: { min: [-60, -2, -60], max: [60, 40, 60], edge: 'wall' }, killZones: [], ramps: [],
    blocks: [B(-14, -14, 1, 1, 7, 'pillar'), B(14, -14, 1, 1, 7, 'pillar'), B(-14, 14, 1, 1, 7, 'pillar'), B(14, 14, 1, 1, 7, 'pillar'),
             B(-32, -8, 1, 1, 7, 'pillar'), B(32, -8, 1, 1, 7, 'pillar'), B(-32, 8, 1, 1, 7, 'pillar'), B(32, 8, 1, 1, 7, 'pillar'),
             B(0, -6, 2, .6, 1, 'crate'), B(-8, 4, .6, 2, 1, 'crate'), B(8, 4, .6, 2, 1, 'crate'), B(0, 22, 3, .6, 1.2, 'crate'),
             B(-26, 26, 5, 4, 5, 'building'), B(26, -26, 5, 4, 5, 'building')],
    spawns: { ffa: spawnRing(46, 16), vanguard: spawnRow(-35, -46, 35, -46, 8), horizon: spawnRow(-35, 46, 35, 46, 8) },
    vehicles: [{ x: 0, z: 12, yaw: 0 }]
  },
  glacier: {   // an ice island: white walls and bunkers, a central plateau reached by two ramps, and four tall ice pillars with gun nests on top
    id: 'glacier', name: 'Glacier Run', half: 70, theme: 'ice', sky: 0xe6f6ff, fog: [70, 300], sun: true, ceiling: 0, lights: [], tint: 0xeaf4fb, accent: 0x6fd3ff, stars: false,
    ground: 0, bounds: { min: [-70, -2, -70], max: [70, 40, 70], edge: 'wall' }, killZones: [],
    ramps: [RAMP(10, 0, 3, 3, 0, 2, 'W'), RAMP(-10, 0, 3, 3, 0, 2, 'E')],
    blocks: [B(0, 0, 7, 7, 2, 'platform'), B(-20, -20, 1.2, 1.2, 8, 'pillar'), B(20, -20, 1.2, 1.2, 8, 'pillar'), B(-20, 20, 1.2, 1.2, 8, 'pillar'), B(20, 20, 1.2, 1.2, 8, 'pillar'),
             B(-30, 0, .8, 10, 3), B(30, 0, .8, 10, 3), B(0, -26, 10, .8, 3), B(0, 26, 10, .8, 3),
             B(-46, -14, 6, 5, 5, 'building'), B(46, 14, 6, 5, 5, 'building'),
             B(-12, -40, 2, .8, 1.2, 'crate'), B(12, -40, 2, .8, 1.2, 'crate'), B(-12, 40, 2, .8, 1.2, 'crate'), B(12, 40, 2, .8, 1.2, 'crate'), B(-8, 14, .8, 2, 1.2, 'crate'), B(8, -14, .8, 2, 1.2, 'crate')],
    spawns: { ffa: spawnRing(56, 24), vanguard: spawnRow(-45, -60, 45, -60, 12), horizon: spawnRow(-45, 60, 45, 60, 12) },
    vehicles: [{ x: -38, z: 0, yaw: 0 }, { x: 38, z: 0, yaw: 0, type: 'tank' }]
  },
  arena: {   // a tight indoor arena: metal walls, doorways, a central block and a ceiling
    id: 'arena', name: 'Sunbaked Fort', half: 24, theme: 'desert', sky: 0xffd27f, fog: [30, 170], sun: true, ceiling: 0, lights: [], tint: 0xe3c196, accent: 0xff9a4d, stars: false,
    ground: 0, bounds: { min: [-24, -2, -24], max: [24, 40, 24], edge: 'wall' }, killZones: [], ramps: [],
    blocks: [B(0, -24.5, 25, .5, 5), B(0, 24.5, 25, .5, 5), B(-24.5, 0, .5, 25, 5), B(24.5, 0, .5, 25, 5),
             B(-12, -10, 6, .5, 4), B(12, -10, 6, .5, 4), B(-12, 10, 6, .5, 4), B(12, 10, 6, .5, 4),
             B(0, 0, 2, 2, 3, 'pillar'), B(-16, 0, .5, 3, 2.5), B(16, 0, .5, 3, 2.5),
             B(-6, -18, 1, 1, 1, 'crate'), B(6, -18, 1, 1, 1, 'crate'), B(-6, 18, 1, 1, 1, 'crate'), B(6, 18, 1, 1, 1, 'crate')],
    spawns: {
      ffa: [...spawnRow(-20, -21, 20, -21, 5), ...spawnRow(-20, 21, 20, 21, 5), at(-20, 0, -6), at(-20, 0, 6), at(20, 0, -6), at(20, 0, 6), at(-10, 0, 0), at(10, 0, 0)],
      vanguard: spawnRow(-20, -21.5, 20, -21.5, 8), horizon: spawnRow(-20, 21.5, 20, 21.5, 8)
    },
    vehicles: [{ x: 0, z: 16, yaw: 0 }]
  },
  station: {   // a floating space station: a deck around an open reactor shaft, raised platforms joined by ramps and skybridges, metal corridors
    id: 'station', name: 'Orbital Station', half: 30, theme: 'night', sky: 0x1f2d66, fog: [70, 280], sun: true, ceiling: 0, lights: [], tint: 0xb4bdd6, accent: 0xb48cff, stars: true, hull: { top: 44, bottom: 14, depth: 20 },
    ground: null, bounds: { min: [-70, -25, -70], max: [70, 60, 70], edge: 'void' },
    killZones: [{ min: [-4, -25, -4], max: [4, -.5, 4], label: 'fell into the reactor shaft' }],
    blocks: [
      B(0, -17, 30, 13, 1, 'deck', -1), B(0, 17, 30, 13, 1, 'deck', -1), B(-17, 0, 13, 4, 1, 'deck', -1), B(17, 0, 13, 4, 1, 'deck', -1),   // the deck, with an 8 x 8 hole in the middle
      B(0, 0, 1.5, 4, .4, 'platform', -.4),                                                                                                  // a catwalk across the shaft
      B(-20, -20, 6, 6, .6, 'platform', 3.4), B(20, -20, 6, 6, .6, 'platform', 3.4), B(-20, 20, 6, 6, .6, 'platform', 3.4), B(20, 20, 6, 6, .6, 'platform', 3.4),   // four raised towers (top at 4 m)
      B(0, -20, 14, 1.5, .6, 'platform', 3.4), B(0, 20, 14, 1.5, .6, 'platform', 3.4),                                                       // skybridges between them
      B(-18, -3.2, 10, .4, 3.6), B(-18, 3.2, 10, .4, 3.6), B(-18, 0, 10, 3.6, .5, 'ceiling', 3.6),                                           // west corridor
      B(18, -3.2, 10, .4, 3.6), B(18, 3.2, 10, .4, 3.6), B(18, 0, 10, 3.6, .5, 'ceiling', 3.6),                                              // east corridor
      B(-10, -10, 1, 1, 1.5, 'crate'), B(10, -10, 1, 1, 1.5, 'crate'), B(-10, 10, 1, 1, 1.5, 'crate'), B(10, 10, 1, 1, 1.5, 'crate'),
      B(-7, -7, .6, .6, 5, 'pillar'), B(7, -7, .6, .6, 5, 'pillar'), B(-7, 7, .6, .6, 5, 'pillar'), B(7, 7, .6, .6, 5, 'pillar')
    ],
    ramps: [RAMP(-20, -9, 2.5, 5, 0, 4, 'N'), RAMP(20, -9, 2.5, 5, 0, 4, 'N'), RAMP(-20, 9, 2.5, 5, 0, 4, 'S'), RAMP(20, 9, 2.5, 5, 0, 4, 'S')],   // ground to tower top, 10 m long
    spawns: {
      ffa: [...spawnRow(-10, -27, 10, -27, 4), ...spawnRow(-10, 27, 10, 27, 4), at(-27, 0, -8), at(27, 0, -8), at(-27, 0, 8), at(27, 0, 8),
            at(-20, 4, -20), at(20, 4, -20), at(-20, 4, 20), at(20, 4, 20)],
      vanguard: [...spawnRow(-12, -27, 12, -27, 6), ...spawnRow(-5, -23.5, 5, -23.5, 2)],
      horizon: [...spawnRow(-12, 27, 12, 27, 6), ...spawnRow(-5, 23.5, 5, 23.5, 2)]
    },
    vehicles: [{ x: 0, z: 12, yaw: 0 }]
  }
};
// ---- Twin Citadels: a 600 x 600 m map (100 times the area of Pillar Fields). Two fortress bases face each other across 360 m of cluttered battlefield.
// It is generated from a fixed seed, so every server builds exactly the same map. In team deathmatch each team spawns deep inside its own base. ----
function buildFrontier() {
  let seed = 20261013; const R = () => (seed = (seed * 16807) % 2147483647) / 2147483647, between = (a, b) => a + (b - a) * R();
  const blocks = [], ramps = [], bases = [], spawns = { ffa: [], vanguard: [], horizon: [] }, vehicles = [], pickups = [], low = [], turrets = [];   // pickups: floating weapons, wi = index into WEAPONS
  const free = (x, z, hx, hz, pad = 2.5) => !blocks.some(o => Math.abs(x - o.x) < hx + o.hx + pad && Math.abs(z - o.z) < hz + o.hz + pad) && !ramps.some(r => Math.abs(x - r.x) < hx + r.hx + pad && Math.abs(z - r.z) < hz + r.hz + pad);
  const mid = (x, z, hx, hz, h, kind, y = 0) => { const b = B(x, z, hx, hz, h, kind, y); blocks.push(b); return b; };
  // The bases are written once in base coordinates (d = metres in from the map edge) and mirrored for the other team. `t` marks a block as a team's, which the browser lights up.
  for (const [team, sz] of [['vanguard', -1], ['horizon', 1]]) {
    const Z = d => sz * (300 - d), dir = { in: sz < 0 ? 'S' : 'N', out: sz < 0 ? 'N' : 'S' };
    const W = (x, d, hx, hd, h, kind = 'wall', y = 0) => { const b = mid(x, Z(d), hx, hd, h, kind, y); b.t = team; return b; };
    W(0, 2, 80, 2, 14); W(-78, 61, 2, 57, 12); W(78, 61, 2, 57, 12); W(-47, 118, 33, 2, 12); W(47, 118, 33, 2, 12);   // back, side and front walls; the gate is the 28 m gap in the front wall
    W(-36, 82, 22, 1.5, 6); W(36, 82, 22, 1.5, 6);                                                                     // an inner defensive line, also with a 28 m opening
    W(0, 40, 20, 8, 5, 'building'); ramps.push(RAMP(0, Z(60.5), 5, 12.5, 0, 5, dir.out));                           // the keep, with a ramp up to its roof; the spawns sit behind it
    for (const x of [-68, 68]) for (const d of [12, 108]) {                                                            // four sniper towers: a 14 m deck reached by a 35 m ramp
      W(x, d, 5, 5, 13.4, 'building'); W(x, d, 7, 7, .6, 'platform', 13.4);
      for (const [px, pd, hx, hd] of [[0, -7, 7, .3], [0, 7, 7, .3], [-7, 0, .3, 7], [7, 0, .3, 7]]) if (pd !== (d === 12 ? 7 : -7)) W(x + px, d + pd, hx, hd, 1.2, 'wall', 14);   // parapet, open where the ramp arrives
      ramps.push(d === 12 ? RAMP(x, Z(36.5), 3, 17.5, 0, 14, dir.out) : RAMP(x, Z(83.5), 3, 17.5, 0, 14, dir.in));
      pickups.push({ wi: 1, x, y: 15.2, z: Z(d) });   // a sniper rifle on every tower deck
    }
    // loose cover in the yard, keeping the two vehicle bays at x = +-30 clear
    for (let i = 0; i < 10; i++) { const x = between(-60, 60), d = between(52, 112); if (Math.abs(x) > 14 && !(d > 90 && Math.abs(Math.abs(x) - 30) < 8) && free(x, Z(d), 1.5, 1.5)) mid(x, Z(d), 1.2, 1.2, 1.2, 'crate'); }   // loose cover in the yard
    bases.push({ team, x: 0, z: Z(60), hx: 76, hz: 56 });
    spawns[team] = [...spawnRow(-24, Z(12), 24, Z(12), 8), ...spawnRow(-24, Z(20), 24, Z(20), 8)];
    const vy = sz < 0 ? Math.PI : 0; vehicles.push({ x: -34, z: Z(100), yaw: vy, type: 'car' }, { x: 34, z: Z(100), yaw: vy, type: 'mech' }, { x: 0, z: Z(96), yaw: vy, type: 'heli' }, { x: 26, z: Z(92), yaw: vy, type: 'tank' });   // a car, a mech and a helicopter in each base
    for (const x of [-17, 17]) { W(x, 110, 1.4, 1.4, 2, 'building'); turrets.push({ team, x, y: 2, z: Z(110) }); }   // a sentry turret on a pedestal either side of the gate
  }
  // The middle: a stepped ziggurat at the centre, then arenas of trenches, pillar fields, tiered platforms and crate yards, then scattered cover.
  const crate = (x, z, s = between(1, 2.2), h = between(1, 2.4)) => { mid(x, z, s, s, h, 'crate'); if (R() < .35) mid(x + between(-.3, .3), z, s * .7, s * .7, h * .7, 'crate', h); };   // sometimes stacked
  mid(0, 0, 24, 24, 2, 'platform'); mid(0, 0, 16, 16, 2, 'platform', 2); mid(0, 0, 8, 8, 2, 'platform', 4);
  for (const s of [-1, 1]) { const d = s > 0 ? 'N' : 'S'; ramps.push(RAMP(0, s * 26.5, 5, 2.5, 0, 2, d), RAMP(0, s * 18.5, 5, 2.5, 2, 4, d), RAMP(0, s * 10.5, 4, 2.5, 4, 6, d), RAMP(s * 26.5, 0, 2.5, 5, 0, 2, s > 0 ? 'W' : 'E')); }
  pickups.push({ wi: 2, x: 0, y: 7.2, z: 0 }, { wi: 1, x: -100, y: 4.8, z: 0 }, { wi: 1, x: 100, y: 4.8, z: 0 });   // a rocket launcher on top of the ziggurat, snipers on the tiered platforms
  for (let i = 0; i < 8; i++) { const a = i * Math.PI / 4; mid(Math.round(38 * Math.cos(a)), Math.round(38 * Math.sin(a)), 1.2, 1.2, 10, 'pillar'); }
  const L = (cx, cz, f, lx, lz, hx, hz, h, kind, y = 0) => mid(cx + (f ? lz : lx), cz + (f ? lx : lz), f ? hz : hx, f ? hx : hz, h, kind, y);   // f turns an arena a quarter turn
  const arena = {
    trench(cx, cz, f) {
      for (const s of [-1, 1]) { L(cx, cz, f, 0, s * 6, 24, .8, 3, 'wall'); L(cx, cz, f, s * 29, 0, 3, 3, 4, 'building'); }
      [-16, 0, 16].forEach((x, i) => L(cx, cz, f, x, i % 2 ? 2.6 : -2.6, .8, 2.6, 2.2, 'wall'));                      // traverses that make you zigzag
      for (let i = 0; i < 4; i++) { const x = cx + (f ? between(-4, 4) : between(-20, 20)), z = cz + (f ? between(-20, 20) : between(-4, 4)); if (free(x, z, 1.2, 1.2, 1)) crate(x, z, 1, 1.2); }
    },
    pillars(cx, cz) { for (let i = -2; i <= 1; i++) for (let j = -2; j <= 1; j++) if (R() < .85) mid(cx + i * 12 + 6, cz + j * 12 + 6, 1.1, 1.1, 9, 'pillar'); },
    tiers(cx, cz) {
      mid(cx, cz, 12, 12, 1.8, 'platform'); mid(cx, cz, 7, 7, 1.8, 'platform', 1.8);
      for (const s of [-1, 1]) { const d = s > 0 ? 'N' : 'S'; ramps.push(RAMP(cx, cz + s * 14.25, 4, 2.25, 0, 1.8, d), RAMP(cx, cz + s * 9.25, 3.5, 2.25, 1.8, 3.6, d)); }
    },
    yard(cx, cz) { for (let i = 0; i < 14; i++) { const x = cx + between(-18, 18), z = cz + between(-18, 18); if (free(x, z, 2.3, 2.3, 1.5)) crate(x, z); } }
  };
  [[-170, -110, 'trench', 0], [170, 110, 'trench', 0], [170, -110, 'pillars'], [-170, 110, 'pillars'], [-100, 0, 'tiers'], [100, 0, 'tiers'], [0, -115, 'yard'], [0, 115, 'yard'],
   [-90, -120, 'yard'], [90, 120, 'yard'], [-240, 0, 'trench', 1], [240, 0, 'trench', 1]].forEach(([x, z, k, f]) => arena[k](x, z, f || 0));
  for (let i = 0; i < 600; i++) {   // scattered cover: crates, pillars, trench walls and low platforms with a ramp
    const x = between(-285, 285), z = between(-172, 172), k = R();
    if (k < .45) { if (free(x, z, 2.5, 2.5, 3)) crate(x, z); }
    else if (k < .7) { if (free(x, z, 1.5, 1.5, 3)) mid(x, z, 1.2, 1.2, between(6, 11), 'pillar'); }
    else if (k < .9) { const f = R() < .5, len = between(5, 12); if (free(x, z, f ? 1 : len, f ? len : 1, 3)) mid(x, z, f ? .8 : len, f ? len : .8, between(2, 3.4), 'wall'); }
    else if (free(x, z + 2, 6, 8, 3)) { mid(x, z, 5, 5, 1.6, 'platform'); ramps.push(RAMP(x, z + 7, 3, 2, 0, 1.6, 'N')); low.push({ x, z }); }
  }
  low.slice(0, 9).forEach((q, i) => pickups.push({ wi: i % 3, x: q.x, y: 2.8, z: q.z }));   // rifle, sniper and rocket in turn on the low platforms
  for (let t = 0; spawns.ffa.length < 20 && t < 3000; t++) { const x = rd(between(-280, 280)), z = rd(between(-165, 165)); if (free(x, z, 1, 1, 3) && spawns.ffa.every(s => Math.hypot(s.x - x, s.z - z) > 40)) spawns.ffa.push(at(x, 0, z)); }
  return {
    id: 'frontier', name: 'Twin Citadels', half: 300, theme: 'grass', sky: 0xc2e7ff, fog: [170, 720], sun: true, big: true, ceiling: 0, lights: [], tint: 0xdde5ec, accent: 0x7ec8ff, stars: false,
    ground: 0, bounds: { min: [-300, -2, -300], max: [300, 60, 300], edge: 'wall' }, killZones: [], blocks, ramps, bases, spawns, vehicles, pickups, turrets
  };
}
MAPS.frontier = buildFrontier();
for (const m of Object.values(MAPS)) {   // manned gun nests on top of the tallest pillars of every map
  m.vehicles = m.vehicles || [];
  const pil = m.blocks.filter(b => b.kind === 'pillar'), top = Math.max(0, ...pil.map(b => b.h));
  if (top >= 7) for (const b of pil) if (b.h === top) m.vehicles.push({ x: b.x, z: b.z, yaw: 0, type: 'turret', y: (b.y || 0) + b.h });
}
const clientMap = m => { const { spawns, ...rest } = m; return rest; };   // players never need the spawn list

// Floors: the ramp's height at a point (t runs 0 at the low end to 1 at the high end), and the highest floor at x, z that is not above yMax.
const rampT = (r, x, z) => {
  const cx = Math.max(r.x - r.hx, Math.min(r.x + r.hx, x)), cz = Math.max(r.z - r.hz, Math.min(r.z + r.hz, z));
  if (r.dir === 'E') return (cx - (r.x - r.hx)) / (2 * r.hx);
  if (r.dir === 'W') return ((r.x + r.hx) - cx) / (2 * r.hx);
  if (r.dir === 'S') return (cz - (r.z - r.hz)) / (2 * r.hz);
  return ((r.z + r.hz) - cz) / (2 * r.hz);
};
const rampY = (r, x, z) => r.y0 + (r.y1 - r.y0) * rampT(r, x, z);
function surfaceY(m, x, z, yMax) {
  let best = m.ground != null && m.ground <= yMax ? m.ground : -Infinity;
  for (const b of m.blocks) { const top = (b.y || 0) + b.h; if (top <= yMax && Math.abs(x - b.x) <= b.hx && Math.abs(z - b.z) <= b.hz) best = Math.max(best, top); }
  for (const r of m.ramps) if (Math.abs(x - r.x) <= r.hx && Math.abs(z - r.z) <= r.hz) { const s = rampY(r, x, z); if (s <= yMax) best = Math.max(best, s); }
  return best;
}
const groundBlock = b => (b.y || 0) < BODY.h && (b.y || 0) + b.h > .05;   // blocks someone walking or driving at ground level can run into
const MAP_IDS = Object.keys(MAPS);
const MAP_ENV = MAPS[process.env.MAP] ? process.env.MAP : 'rotate';

// Each room is its own match: its own players, bots, map, vehicles and timers. The functions below are written against "the current room"
// (players, match, map, vehicles ...), and inRoom(room, fn) points those at one room while fn runs, then saves them back. Node runs one
// handler at a time, so a room can never see another room's state: bots, hits, spawns and scores all stay inside their own room.
let players, match, map = MAPS.field, vehicles = [], tick = 0, nextTimer = null, spawnHeld, pickups, turrets, cur = null;   // the current room's state
let nextId = 1, spawnIx = 0;                                                                              // ids are unique across all rooms

const app = express();
if (process.env.SITE_DIR) app.use(express.static(path.resolve(process.env.SITE_DIR)));   // optional: serve the arcade locally too
app.get('/health', (req, res) => res.json({ ok: true, players: [...rooms.values()].reduce((n, r) => n + r.players.size, 0), rooms: [...rooms.values()].map(r => ({ id: r.id, humans: humansIn(r), players: r.players.size, mode: r.match.mode, map: r.map.id })) }));

const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: (origin, cb) => cb(null, !origin || ORIGINS.includes(origin) || /^http:\/\/(localhost|127\.0\.0\.1)(:\d+)?$/.test(origin)) },
  maxHttpBufferSize: 1e4
});

const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));
const wrap = a => ((a + Math.PI) % (2 * Math.PI) + 2 * Math.PI) % (2 * Math.PI) - Math.PI;
const r2 = v => Math.round(v * 100) / 100, r3 = v => Math.round(v * 1000) / 1000;
const W = p => WEAPONS[p.wi];
// Exoskeleton frame of a player or bot. It only counts if it is owned (an unowned id in a profile falls back to the free Raider), so nobody can wear what they have not bought.
const frameOf = p => { const pr = profOf(p), f = skinById.get(pr.eq.frame); return f && f.slot === 'frame' && pr.owned.includes(f.id) ? f.fr : skinById.get('f-raider').fr; };
const maxHp = p => frameOf(p).hp;
const MELEE_DMG = 40, MELEE_RANGE = 2.6;
const pub = p => ({ id: p.id, name: p.name, lv: lvOf(p), faction: p.faction, kills: p.kills, deaths: p.deaths, alive: p.alive, x: p.x, y: p.y, z: p.z, yaw: p.yaw, pitch: p.pitch, skin: { body: profOf(p).eq.body, weapon: profOf(p).eq.weapon, frame: profOf(p).eq.frame } });
const matchInfo = () => ({ mode: match.mode, limit: LIMIT[match.mode], state: match.state, team: match.team, map: map.name });
const sendScores = () => emit('scores', { t: match.team, p: [...players.values()].map(p => [p.id, p.kills, p.deaths, lvOf(p)]) });
const vehRows = () => vehicles.map(v => [v.id, r2(v.x), r2(v.z), r3(v.yaw), v.driver ? v.driver.id : 0, r2(v.y || 0), v.gunner ? v.gunner.id : 0]);
function profileView(p) {
  const pr = profOf(p), lv = levelInfo(pr.xp);
  return { xp: pr.xp, level: lv.level, into: lv.into, need: lv.need, coins: pr.coins, kills: pr.kills, owned: pr.owned, eq: pr.eq, save: sign(p.token, pr) };
}
const notice = (p, text, extra) => p.sock.emit('notice', { text, ...extra });
function grant(p, xp, coins, why) {
  if (p.bot) { p.prof.xp += xp; p.prof.coins += coins; return; }   // a bot's profile is a fake one: it earns coins on paper but is never saved   // XP and coins go to the player's saved profile; a level-up pays a bonus
  const pr = profOf(p), before = levelInfo(pr.xp).level;
  pr.xp += xp; pr.coins += coins; if (why === 'kill') pr.kills++;
  const up = levelInfo(pr.xp).level - before, bonus = up > 0 ? LEVEL_UP_COINS * up : 0;
  pr.coins += bonus; pr.rev++; store.set(p.token, pr);
  p.sock.emit('profile', { ...profileView(p), gain: { xp, coins: coins + bonus, why }, levelUp: up > 0 });
}
function equip(p, s) {   // wear a skin and tell everyone, so they see it too
  const pr = profOf(p); pr.eq[s.slot] = s.id; pr.rev++; store.set(p.token, pr);
  p.sock.emit('profile', profileView(p));
  emit('skin', { id: p.id, body: pr.eq.body, weapon: pr.eq.weapon, frame: pr.eq.frame });
}
const emitYou = p => p.sock.emit('you', { hp: p.hp, ammos: p.ammos, reserve: p.reserve, held: [...p.held], wi: p.wi, reloading: !!p.reloadEnd });
const profOf = p => { const s = store.get(p.token); if (s) p.prof = s; return p.prof; };   // two tabs of one browser share one profile
const cleanName = (n, id) => (typeof n === 'string' ? n.replace(/[^\p{L}\p{N} _.-]/gu, '').trim().slice(0, 14) : '') || 'Pilot ' + id;
const safeEqual = (a, b) => { const x = Buffer.from(a), y = Buffer.from(b); return x.length === y.length && crypto.timingSafeEqual(x, y); };

// New players: random side in team deathmatch, but if the teams are uneven the smaller one gets them.
function pickFaction() {
  if (match.mode !== 'tdm') return 'ffa';
  let v = 0, h = 0;
  for (const p of players.values()) { if (p.faction === 'vanguard') v++; else if (p.faction === 'horizon') h++; }
  if (v === h) return Math.random() < .5 ? 'vanguard' : 'horizon';
  return v < h ? 'vanguard' : 'horizon';
}

// The spawn matrix: pick the point (from this mode's list for this player) that is farthest from everyone alive, counting enemies
// as closer than they are; skip points that were just used, so players arriving together never share one.
// spawnHeld (per room): spawn point -> when it was last used
function pickSpawn(p) {
  const list = (match.mode === 'tdm' && map.spawns[p.faction]) || map.spawns.ffa, now = Date.now();
  let best = list[0], bestScore = -Infinity;
  for (const sp of list) {
    let near = 100;
    for (const q of players.values()) {
      if (q === p || !q.alive) continue;
      const enemy = !(match.mode === 'tdm' && q.faction === p.faction);
      near = Math.min(near, Math.hypot(q.x - sp.x, q.y - sp.y, q.z - sp.z) * (enemy ? .7 : 1));
    }
    const score = near - (now - (spawnHeld.get(sp) || 0) < 2500 ? 1000 : 0) + Math.random() * 3;   // a little jitter keeps spawns unpredictable
    if (score > bestScore) { best = sp; bestScore = score; }
  }
  spawnHeld.set(best, now);
  return best;
}

function respawn(p) {
  const sp = pickSpawn(p);
  Object.assign(p, { x: sp.x, y: sp.y, z: sp.z, yaw: sp.yaw, pitch: 0, hp: maxHp(p), alive: true, wi: 0, ammos: WEAPONS.map(w => w.magazineSize), reserve: WEAPONS.map(w => w.maxAmmo), held: new Set(), reloadEnd: 0, nextShot: 0, vehicle: 0, epoch: p.epoch + 1, hist: [] });
  p.sock.emit('respawn', { x: sp.x, y: sp.y, z: sp.z, yaw: sp.yaw, hp: p.hp, maxHp: maxHp(p), ammos: p.ammos, reserve: p.reserve, wi: p.wi, e: p.epoch });   // e: old position updates still in flight are ignored
}

function startReload(p) {
  if (p.reloadEnd || p.ammos[p.wi] >= W(p).magazineSize || p.reserve[p.wi] <= 0) return;
  p.reloadEnd = Date.now() + W(p).reloadTime * 1000;
  emitYou(p);
}

// ---- geometry helpers ----
// Ray against an axis-aligned box (slab method). Returns the distance along the ray, or null for a miss.
function rayBox(o, d, x0, y0, z0, x1, y1, z1) {
  const O = [o.x, o.y, o.z], D = [d.x, d.y, d.z], lo = [x0, y0, z0], hi = [x1, y1, z1];
  let tmin = 0, tmax = Infinity;
  for (let i = 0; i < 3; i++) {
    if (Math.abs(D[i]) < 1e-9) { if (O[i] < lo[i] || O[i] > hi[i]) return null; continue; }
    let a = (lo[i] - O[i]) / D[i], b = (hi[i] - O[i]) / D[i];
    if (a > b) [a, b] = [b, a];
    tmin = Math.max(tmin, a); tmax = Math.min(tmax, b);
    if (tmin > tmax) return null;
  }
  return tmin;
}
// A ramp is a wedge: every point below its sloped top, between its two ends and two sides. Cut the ray with each of those five flat faces.
function rayRamp(o, d, r) {
  const alongX = r.dir === 'E' || r.dir === 'W', sgn = r.dir === 'E' || r.dir === 'S' ? 1 : -1;
  const half = alongX ? r.hx : r.hz, c0 = alongX ? r.x : r.z, hw = alongX ? r.hz : r.hx, w0 = alongX ? r.z : r.x, slope = (r.y1 - r.y0) / (2 * half);
  // planes as [nx, ny, nz, c]: a point is inside when nx*x + ny*y + nz*z <= c
  const A = (a, y, b, c) => alongX ? [a, y, b, c] : [b, y, a, c];             // a = the climbing axis, b = across it
  const planes = [
    A(sgn, 0, 0, half + sgn * c0), A(-sgn, 0, 0, half - sgn * c0),            // the two ends
    A(0, 0, 1, w0 + hw), A(0, 0, -1, -(w0 - hw)),                             // the two sides
    [0, -1, 0, -(Math.min(r.y0, r.y1) - 1)],                                  // the base
    A(-slope * sgn, 1, 0, r.y0 + slope * (half - sgn * c0))                   // the slope
  ];
  let tmin = 0, tmax = Infinity;
  for (const [nx, ny, nz, c] of planes) {
    const den = nx * d.x + ny * d.y + nz * d.z, num = c - (nx * o.x + ny * o.y + nz * o.z);
    if (Math.abs(den) < 1e-9) { if (num < 0) return null; continue; }
    const t = num / den;
    if (den < 0) tmin = Math.max(tmin, t); else tmax = Math.min(tmax, t);
    if (tmin > tmax) return null;
  }
  return tmin;
}
// The vehicle box is turned by its yaw, so rotate the ray into the vehicle's own frame first.
function rayVehicle(o, d, v) {
  const c = Math.cos(v.yaw), s = Math.sin(v.yaw), dx = o.x - v.x, dz = o.z - v.z;
  return rayBox({ x: dx * c - dz * s, y: o.y, z: dx * s + dz * c }, { x: d.x * c - d.z * s, y: d.y, z: d.x * s + d.z * c }, -vd(v).hx, v.y || 0, -vd(v).hz, vd(v).hx, (v.y || 0) + vd(v).h, vd(v).hz);
}
function distToVehicle(v, x, z) {   // ground-plane distance from a point to the vehicle's body (0 = touching)
  const c = Math.cos(v.yaw), s = Math.sin(v.yaw), dx = x - v.x, dz = z - v.z;
  return Math.hypot(Math.max(Math.abs(dx * c - dz * s) - vd(v).hx, 0), Math.max(Math.abs(dx * s + dz * c) - vd(v).hz, 0));
}
function exitSpot(v) {   // first free spot beside the vehicle: right, left, behind, in front. It must be on a floor, clear of walls and kill zones
  const c = Math.cos(v.yaw), s = Math.sin(v.yaw), lim = map.half - BODY.r;
  const solid = [...map.blocks.filter(groundBlock), ...map.ramps, ...map.killZones.map(k => ({ x: (k.min[0] + k.max[0]) / 2, z: (k.min[2] + k.max[2]) / 2, hx: (k.max[0] - k.min[0]) / 2, hz: (k.max[2] - k.min[2]) / 2 }))];
  for (const [lx, lz] of [[vd(v).hx + 1, 0], [-vd(v).hx - 1, 0], [0, vd(v).hz + 1], [0, -vd(v).hz - 1]]) {
    const x = v.x + lx * c + lz * s, z = v.z - lx * s + lz * c;
    if (Math.abs(x) <= lim && Math.abs(z) <= lim && surfaceY(map, x, z, .1) > -.05 && !solid.some(b => Math.abs(x - b.x) < b.hx + BODY.r && Math.abs(z - b.z) < b.hz + BODY.r)) return { x, z };
  }
  return { x: v.x, z: v.z };
}

// Where was this player at time t? Used to rewind targets to what the shooter was actually seeing (lag compensation).
function posAt(p, t) {
  const h = p.hist, n = h.length;
  if (!n || t >= h[n - 1].t) return p;
  if (t <= h[0].t) return h[0];
  let i = n - 1; while (i > 1 && h[i - 1].t > t) i--;
  const a = h[i - 1], b = h[i], k = (t - a.t) / ((b.t - a.t) || 1);
  return { x: a.x + (b.x - a.x) * k, y: a.y + (b.y - a.y) * k, z: a.z + (b.z - a.z) * k };
}

// Nearest thing the shot hits: floor, block, vehicle (the driver is exposed), or a living enemy on foot.
function cast(shooter, o, d, range) {
  const friend = p => match.mode === 'tdm' && p.faction === shooter.faction;
  let best = { t: range, who: null };
  if (map.ground != null && d.y < -1e-6) { const t = (map.ground - o.y) / d.y; if (t > 0 && t < best.t) best = { t, who: null }; }
  for (const b of map.blocks) {
    const y0 = b.y || 0, t = rayBox(o, d, b.x - b.hx, y0, b.z - b.hz, b.x + b.hx, y0 + b.h, b.z + b.hz);
    if (t !== null && t < best.t) best = { t, who: null };
  }
  for (const r of map.ramps) { const t = rayRamp(o, d, r); if (t !== null && t < best.t) best = { t, who: null }; }
  for (const v of vehicles) {
    if (v.driver === shooter) continue;   // never shoot your own vehicle
    const t = rayVehicle(o, d, v);
    if (t !== null && t < best.t) best = { t, who: v.driver && v.driver !== shooter && !friend(v.driver) ? v.driver : null };
  }
  const when = Date.now() - Math.min(400, shooter.rtt + 100);   // round trip plus the 100 ms clients draw others in the past
  for (const p of players.values()) {
    if (p === shooter || !p.alive || p.vehicle || friend(p)) continue;   // no friendly fire; drivers are covered by the vehicle above
    const q = posAt(p, when);
    const t = rayBox(o, d, q.x - BODY.r, q.y, q.z - BODY.r, q.x + BODY.r, q.y + BODY.h, q.z + BODY.r);
    if (t !== null && t < best.t) best = { t, who: p, head: rayBox(o, d, q.x - .22, q.y + 1.45, q.z - .22, q.x + .22, q.y + BODY.h, q.z + .22) !== null };   // the head is a small box on top of the body box
  }
  return best;
}

function leaveVehicle(p, notify) {
  const v = vehicles.find(x => x.id === p.vehicle);
  p.vehicle = 0; p.seat = 0;
  if (!v) return;
  if (v.gunner === p) v.gunner = null;   // a roof gunner steps off and the driver carries on
  else { v.driver = null; v.speed = 0; v.y = v.sy || 0; if (v.gunner) leaveVehicle(v.gunner, true); }   // an empty helicopter settles; a gunner is put out with the driver
  if (notify) { const s = exitSpot(v); p.x = s.x; p.z = s.z; p.y = 0; p.sock.emit('undrive', { x: s.x, z: s.z }); }
  emit('vehicles', vehRows());
}

function hurt(shooter, target, dmg, head, how) {
  target.hp -= dmg;
  const dead = target.hp <= 0;
  shooter.sock.emit('hit', { kill: dead, head: !!head });
  if (!dead) { emitYou(target); return; }
  target.hp = 0; target.alive = false; target.deaths++; shooter.kills++; target.respawnAt = Date.now() + RESPAWN_MS; target.reloadEnd = 0;
  if (target.vehicle) leaveVehicle(target, false);
  dropWeapon(target);   // the weapon they held floats where they fell
  if (match.mode === 'tdm') match.team[shooter.faction]++;
  grant(shooter, XP_PER_KILL, COINS_PER_KILL, 'kill');
  emitYou(target);
  emit('kill', { k: shooter.id, v: target.id, kn: shooter.name, vn: target.name, kf: shooter.faction, vf: target.faction, kl: lvOf(shooter), vl: lvOf(target), hs: !!head, how: how || '', r: RESPAWN_MS });
  sendScores();
  if (match.mode === 'tdm' && match.team[shooter.faction] >= LIMIT.tdm) endMatch(shooter.faction.toUpperCase() + ' WINS', shooter.faction, [...players.values()].filter(p => p.faction === shooter.faction));
  else if (match.mode === 'ffa' && shooter.kills >= LIMIT.ffa) endMatch(shooter.name + ' WINS', 'ffa', [shooter]);
}

// Out of bounds: leave the play box, fall below its floor, or enter a kill zone and you are eliminated (no killer, no points).
function oobReason(p) {
  const b = map.bounds;
  if (p.x < b.min[0] || p.x > b.max[0] || p.y < b.min[1] || p.y > b.max[1] || p.z < b.min[2] || p.z > b.max[2]) return 'fell out of the arena';
  for (const k of map.killZones) if (p.x >= k.min[0] && p.x <= k.max[0] && p.y >= k.min[1] && p.y <= k.max[1] && p.z >= k.min[2] && p.z <= k.max[2]) return k.label;
  return null;
}
function eliminate(p, why) {
  p.hp = 0; p.alive = false; p.deaths++; p.respawnAt = Date.now() + RESPAWN_MS; p.reloadEnd = 0;
  if (p.vehicle) leaveVehicle(p, false);
  emitYou(p);
  emit('kill', { k: 0, v: p.id, kn: '', vn: p.name, kf: 'ffa', vf: p.faction, vl: lvOf(p), r: RESPAWN_MS, why });
  sendScores();
}

// A map is only used if its spawn matrix is safe: inside the bounds, standing on a floor, clear of walls and kill zones, with head room,
// 3.5 m apart, and enough points for a full server. Returns a list of problems (empty = good). Runs for every map at startup.
function validateMap(m) {
  const bad = [], b = m.bounds, R = BODY.r;
  const inBox = (x, y, z) => x >= b.min[0] && x <= b.max[0] && y >= b.min[1] && y <= b.max[1] && z >= b.min[2] && z <= b.max[2];
  const need = { ffa: MAX_PLAYERS, vanguard: MAX_PLAYERS / 2, horizon: MAX_PLAYERS / 2 };
  for (const name of Object.keys(need)) {
    const pts = m.spawns[name] || [];
    if (pts.length < need[name]) bad.push(name + ' needs at least ' + need[name] + ' spawn points (has ' + pts.length + ')');
    pts.forEach((s, i) => {
      const tag = name + '#' + i;
      if (!inBox(s.x, s.y + 1, s.z) || (b.edge === 'wall' && (Math.abs(s.x) > m.half - R || Math.abs(s.z) > m.half - R))) bad.push(tag + ' is outside the boundary');
      if (Math.abs(surfaceY(m, s.x, s.z, s.y + .05) - s.y) > .05) bad.push(tag + ' is not standing on a floor');
      for (const k of m.blocks) if (Math.abs(s.x - k.x) < k.hx + R && Math.abs(s.z - k.z) < k.hz + R && (k.y || 0) + k.h > s.y + .05 && (k.y || 0) < s.y + BODY.h) bad.push(tag + ' is inside a ' + k.kind);
      for (const r of m.ramps) if (Math.abs(s.x - r.x) < r.hx + R && Math.abs(s.z - r.z) < r.hz + R) bad.push(tag + ' is on a ramp');
      for (const k of m.killZones) if (s.x >= k.min[0] - R && s.x <= k.max[0] + R && s.z >= k.min[2] - R && s.z <= k.max[2] + R && s.y <= k.max[1] + 1.8) bad.push(tag + ' is in a kill zone');
      if (!Number.isFinite(s.yaw)) bad.push(tag + ' has no facing');
    });
    for (let i = 0; i < pts.length; i++) for (let j = i + 1; j < pts.length; j++) if (Math.hypot(pts[i].x - pts[j].x, pts[i].y - pts[j].y, pts[i].z - pts[j].z) < 3.5) bad.push(name + '#' + i + ' and #' + j + ' are less than 3.5 m apart');
  }
  m.vehicles.forEach((v, i) => {
    if (v.type === 'turret') return;   // a pillar gun nest sits on top of its pillar on purpose
    if (m.blocks.some(k => groundBlock(k) && Math.abs(v.x - k.x) < k.hx + (VTYPES[v.type || 'car'].hx) && Math.abs(v.z - k.z) < k.hz + (VTYPES[v.type || 'car'].hz))) bad.push('vehicle#' + i + ' is inside a block');
    if (surfaceY(m, v.x, v.z, .1) < -.05) bad.push('vehicle#' + i + ' is not on a floor');
  });
  return bad;
}

// ---- matches and maps ----
const nextMapId = () => MAP_ENV !== 'rotate' ? MAP_ENV : MAP_IDS[(MAP_IDS.indexOf(map.id) + 1) % MAP_IDS.length];

function endMatch(winner, wf, winners) {
  if (match.state !== 'live') return;
  match.state = 'over';
  for (const p of winners || []) grant(p, 0, WIN_COINS, 'win');
  const next = MODE === 'rotate' ? (match.mode === 'tdm' ? 'ffa' : 'tdm') : match.mode, nextMap = nextMapId();
  emit('match', { ...matchInfo(), winner, wf, next, nextMap: MAPS[nextMap].name, ms: INTERMISSION_MS });
  { const room = cur; nextTimer = setTimeout(() => inRoom(room, () => startMatch(next, nextMap)), INTERMISSION_MS); }   // the timer fires outside any room, so re-enter this one
}

function startMatch(mode, mapId) {
  clearTimeout(nextTimer);
  map = MAPS[mapId] || map;
  match.mode = mode; match.state = 'live'; match.team = { vanguard: 0, horizon: 0 };
  vehicles = map.vehicles.map((d, i) => ({ id: i + 1, type: d.type || 'car', x: d.x, y: d.y || 0, sy: d.y || 0, z: d.z, yaw: d.yaw, speed: 0, driver: null, gunner: null, dirty: false, heat: 0, lockUntil: 0 }));
  for (const p of players.values()) p.vehicle = 0;
  const list = [...players.values()].sort(() => Math.random() - .5), flip = Math.random() < .5 ? 1 : 0;   // random split into teams
  list.forEach((p, i) => { p.kills = p.deaths = 0; p.faction = mode === 'tdm' ? ((i + flip) % 2 ? 'horizon' : 'vanguard') : 'ffa'; });
  emit('map', clientMap(map));
  pickups = (map.pickups || []).map((d, i) => ({ id: 'm' + i, wi: d.wi, x: d.x, y: d.y, z: d.z, up: true, back: 0, drop: false })); emit('pk', pickupRows()); makeTurrets();
  emit('vehicles', vehRows());
  emit('match', matchInfo());
  emit('factions', list.map(p => [p.id, p.faction]));
  for (const p of players.values()) p.alive = false;   // so each new spawn only has to keep clear of players already placed
  for (const p of players.values()) respawn(p);
  sendScores();
}

// Host control: load a map and/or mode right now (see the comment at the top).
app.get('/admin', (req, res) => {
  const key = process.env.ADMIN_KEY, q = req.query || {};
  if (!key || !safeEqual(String(q.key || ''), key)) return res.status(403).json({ ok: false, error: 'forbidden' });
  if (q.map !== undefined && !MAPS[q.map]) return res.status(400).json({ ok: false, error: 'unknown map', maps: MAP_IDS });
  if (q.mode !== undefined && !['tdm', 'ffa'].includes(q.mode)) return res.status(400).json({ ok: false, error: 'mode must be tdm or ffa' });
  const room = rooms.get(q.room) || rooms.values().next().value || createRoom();   // ?room=Server-US-1, otherwise the oldest room
  inRoom(room, () => { if (q.map !== undefined || q.mode !== undefined) startMatch(q.mode || match.mode, q.map || map.id); });
  res.json({ ok: true, room: room.id, map: room.map.id, mode: room.match.mode, maps: MAP_IDS, rooms: [...rooms.keys()] });
});

// ---- bots: fake players that fill every empty slot and hunt. They are real entries in `players`, so scoring, spawning, lag compensation and
// snapshots treat them like anyone else; the server moves and shoots for them. Set BOTS=off to switch them off. With no human connected
// there are no bots (nobody to hunt, and the host's CPU is free). ----
const BOTS_ON = process.env.BOTS !== 'off', BOT = { speed: 5.4, turn: .22, jump: 7.5, gravity: 22, step: .6 };
const coolNames = [
  'Xenon_Striker', 'Vortex_11', 'ApexPredator', 'Nova_Prime', 'Ghost_Protocol', 'Cyber_Samurai', 'Matrix_Echo', 'Void_Walker', 'Quantum_Spectre', 'Hyperion_Rex',
  'Neon_Glitch', 'Alpha_Enforcer', 'Shadow_Phreak', 'Chronos_Zero', 'Plasma_Pulse', 'Titan_Shard', 'Cipher_Wraith', 'Orbit_Reaper', 'Photon_Hawk', 'Static_Reign',
  'Zenith_Blade', 'Iron_Halcyon', 'Rogue_Vector', 'Nebula_Fang', 'Astra_Viper', 'Binary_Ronin', 'Cobalt_Revenant', 'Delta_Phantom', 'Echo_Marauder', 'Flux_Warden',
  'Gamma_Raptor', 'Helix_Hunter', 'Ion_Sentinel', 'Jetstream_X', 'Kilo_Havoc', 'Lunar_Sniper', 'Mecha_Fury', 'Nexus_Rogue', 'Omega_Drift', 'Pulsar_Zero',
  'Quasar_Knight', 'Radiant_Wolf', 'Solar_Reaper', 'Tachyon_Kid', 'Umbra_Strike', 'Vector_Prime', 'Warp_Drifter', 'Xeno_Havoc', 'Yotta_Storm', 'Zero_Cool',
  'Arc_Welder', 'Blitz_Orbit', 'Cryo_Saber', 'Dark_Matter', 'Ember_Circuit', 'Fusion_Core', 'Gravity_Well', 'Hex_Raider', 'Ionic_Fox', 'Jade_Cipher',
  'Kinetic_Rush', 'Laser_Lynx', 'Mach_Nine', 'Neutron_Star', 'Onyx_Ranger', 'Proton_Wraith', 'Quartz_Hunter', 'Rift_Walker', 'Sigma_Strike', 'Terra_Forge',
  'Ultra_Vortex', 'Vanta_Black', 'Wraith_Circuit', 'Xylo_Phantom', 'Zephyr_Prime', 'Apex_Glitch', 'Byte_Reaper', 'Cinder_Nova', 'Drone_Slayer', 'Eclipse_Rider',
  'Falcon_Nine', 'Ghost_Signal', 'Hollow_Point', 'Icarus_Rising', 'Kryptic_Nova', 'Lancer_One', 'Mirage_Unit', 'Night_Circuit', 'Orion_Strike', 'Pixel_Reaper'
];
const sillyNames = [
  'CheekyApple', 'ToastyWaffle', 'SoggyBiscuit', 'GrumpyPotato', 'SillyGoose99', 'Banananator', 'DrunkMuffin', 'ClumsyNinja', 'TacticalTaco', 'CrispyBacon',
  'YeetMachine', 'McNuggetWarrior', 'ButterFinger', 'NoodleSoup', 'PicklePanic', 'WobblyPenguin', 'SneakyPancake', 'LlamaDrama', 'CaptainCrumpet', 'DizzyDonut',
  'FluffyNuke', 'GassyGiraffe', 'HamsterOverlord', 'JellyBeanJoe', 'KettleKing', 'LazyLasagna', 'MightyMeatball', 'NachoAverageNoob', 'OopsAllBullets', 'PotatoAim',
  'QuackAttack', 'RampantRaccoon', 'SirLagsALot', 'TurboTurnip', 'UnluckyUnicorn', 'VeggieViking', 'WaffleWizard', 'BoopTheSnoot', 'CrumbCommander', 'DuckDuckBoom'
];
const BOT_SOCK = { emit() {} };   // a bot has no browser: anything sent to it is dropped
const randOf = a => a[Math.floor(Math.random() * a.length)];
const lvOf = p => (p.bot ? p.lv : levelInfo(profOf(p).xp).level);   // bots wear a fake level, people their real one
const nameTaken = (nm, except) => { const l = nm.toLowerCase(); for (const p of players.values()) if (p !== except && p.name.toLowerCase() === l) return true; return false; };
function botName() {   // 23% silly, 77% sci-fi, never a name already in this room (only unused names are candidates, which is the retry loop without the waiting)
  const unused = list => list.filter(n => !nameTaken(n));
  let list = unused(Math.random() < .23 ? sillyNames : coolNames);
  if (!list.length) list = unused(coolNames.concat(sillyNames));
  return list.length ? randOf(list) : 'Unit_' + nextId;
}
function spawnBot() {
  const id = nextId++, body = randOf(PREMIUM), weapon = randOf(SKINS.filter(s => s.slot === 'weapon')).id, frame = randOf(SKINS.filter(s => s.slot === 'frame')).id;   // every bot: a random premium skin and a random exoskeleton
  const b = {
    id, key: 'bot' + id, bot: true, sock: BOT_SOCK, token: null, prof: { xp: 0, coins: 0, kills: 0, owned: [body, weapon, frame], eq: { body, weapon, frame } },
    lv: 5 + Math.floor(Math.random() * 91), shopAt: 0, name: botName(), faction: pickFaction(), x: 0, y: 0, z: 0, yaw: 0, pitch: 0, last: 0, lastVeh: 0, useAt: 0,
    hp: HP, alive: true, kills: 0, deaths: 0, ammos: WEAPONS.map(w => w.magazineSize), reserve: WEAPONS.map(w => w.maxAmmo), held: new Set(), wi: 0, vehicle: 0, reloadEnd: 0, nextShot: 0,
    respawnAt: 0, epoch: 0, rtt: 0, hist: [], nameAt: 0, vy: 0, onGround: true, strafe: 1, strafeAt: 0, stuck: 0, detourUntil: 0, detour: 0, panic: null, goal: null, goalAt: 0
  };
  b.hp = maxHp(b);
  b.wi = randOf(WEAPONS.map((w, i) => i).filter(i => WEAPONS[i].unlockLevel <= b.lv));   // a bot only starts with a weapon its fake level has unlocked
  const sp = pickSpawn(b); Object.assign(b, { x: sp.x, y: sp.y, z: sp.z, yaw: sp.yaw });
  players.set(b.key, b); emit('join', pub(b)); sendScores();
}
function removeBot(b) { if (b.vehicle) leaveVehicle(b, false); players.delete(b.key); emit('leave', b.id); }
function kickBot() { const bots = [...players.values()].filter(p => p.bot); if (!bots.length) return false; removeBot(randOf(bots)); return true; }   // a person arrived: a bot makes room
function balanceBots() {   // keep the room full: humans + bots = MAX_PLAYERS
  const humans = [...players.values()].filter(p => !p.bot).length;
  if (!BOTS_ON || !humans) { for (const p of [...players.values()]) if (p.bot) removeBot(p); return; }
  while (players.size < MAX_PLAYERS) spawnBot();
}

// Can a bot stand at x, z? Not through walls, kill zones or the edge of the world, and not over a drop with no floor while on the ground.
function botBlocked(p, x, z) {
  const b = map.bounds; if (x < b.min[0] + 1 || x > b.max[0] - 1 || z < b.min[2] + 1 || z > b.max[2] - 1) return true;
  for (const k of map.blocks) { const y0 = k.y || 0; if (y0 + k.h > p.y + BOT.step && y0 < p.y + BODY.h && Math.abs(x - k.x) < k.hx + BODY.r && Math.abs(z - k.z) < k.hz + BODY.r) return true; }
  for (const k of map.killZones) if (x >= k.min[0] - 1 && x <= k.max[0] + 1 && z >= k.min[2] - 1 && z <= k.max[2] + 1 && p.y <= k.max[1] + 1) return true;
  return p.onGround && surfaceY(map, x, z, p.y + BOT.step) === -Infinity;
}
// Every tick each living bot hunts: it finds the closest living enemy (anyone, in FFA), turns toward them, runs at them and shoots with a
// little aim error. With nobody left alive it sprints between busy spots (the spawn points and the middle) to find a fight.
const botSkill = lv => clamp(.1 + .72 * (lv - 5) / 90 + (Math.random() - .5) * .3, .06, .88);   // 0 hopeless .. 1 perfect: follows the fake level, jittered so equal levels differ, capped so nobody is perfect
function steer(p, mx, mz) {   // the clear heading nearest to where the bot wants to go, probing 1.5 m and 3.2 m ahead, so it slides along a wall instead of pushing into it
  const a0 = Math.atan2(mz, mx), s = p.side || 1;
  for (const off of [0, .45, -.45, .9, -.9, 1.4, -1.4, 2, -2]) {
    const a = a0 + off * s, c = Math.cos(a), n = Math.sin(a);
    if (!botBlocked(p, p.x + c * 1.5, p.z + n * 1.5) && !botBlocked(p, p.x + c * 3.2, p.z + n * 3.2)) return [c, n];
  }
  return [-mx, -mz];   // boxed in: back out
}
function botTick(now) {
  const dt = 1 / TICK_HZ;
  for (const p of players.values()) {
    if (!p.bot) continue;
    if (!p.alive || match.state !== 'live') { p.vy = 0; p.panic = null; continue; }
    if (p.vehicle) { botDrive(p, now, dt); continue; }
    if (now > (p.boardAt || 0)) {   // an empty vehicle within reach on the way: press E
      p.boardAt = now + 700; const v = vehicles.find(x => !x.driver && Math.abs((x.y || 0) - p.y) < 3 && distToVehicle(x, p.x, p.z) < 2.2);
      if (v && Math.random() < .75) { v.driver = p; p.vehicle = v.id; p.reloadEnd = 0; p.drove = now; p.stuck = 0; v.speed = 0; v.dirty = true; emit('vehicles', vehRows()); continue; }
    }
    const skill = p.skill ?? (p.skill = botSkill(p.lv)), turnR = BOT.turn * (.4 + .7 * skill);
    let tgt = null, best = Infinity;
    for (const q of players.values()) {
      if (q === p || !q.alive || (match.mode === 'tdm' && q.faction === p.faction)) continue;
      const d = Math.hypot(q.x - p.x, q.y - p.y, q.z - p.z); if (d < best) { best = d; tgt = q; }
    }
    if (tgt !== p.lastTgt) { p.lastTgt = tgt; p.reactAt = now + (900 - 700 * skill) + Math.random() * 400; }   // a new target takes a moment to notice: slower for weaker bots
    if (tgt && now > (p.wsAt || 0) && !p.reloadEnd) { p.wsAt = now + 1200; const have = i => i === 0 || (p.held.has(i) && (p.ammos[i] > 0 || p.reserve[i] > 0)); const pick = best > 70 && have(1) ? 1 : best > 14 && best < 90 && have(2) && Math.random() < .5 ? 2 : 0; if (pick !== p.wi) p.wi = pick; }   // sniper at range, rockets mid range, rifle up close
    if (!tgt && (!p.goal || now > p.goalAt || Math.hypot(p.goal.x - p.x, p.goal.z - p.z) < 3)) { p.goal = Math.random() < .3 ? { x: 0, z: 0 } : randOf(map.spawns.ffa); p.goalAt = now + 8000; }
    const gx = tgt ? tgt.x : p.goal.x, gy = tgt ? tgt.y + 1.2 : p.y + BODY.eye, gz = tgt ? tgt.z : p.goal.z;
    const dx = gx - p.x, dy = gy - (p.y + BODY.eye), dz = gz - p.z, flat = Math.hypot(dx, dz) || 1, dist = Math.hypot(dx, dy, dz) || 1;   // the 3D vector to the target
    const wantYaw = Math.atan2(-dx, -dz);
    p.yaw = r3(wrap(p.yaw + clamp(wrap(wantYaw - p.yaw), -turnR, turnR)));                                      // turn smoothly, never snap
    p.pitch = r3(clamp(p.pitch + clamp(Math.atan2(dy, flat) - p.pitch, -.12, .12), -1.2, 1.2));
    if (p.hp >= maxHp(p) * .3) p.panic = null; else if (p.panic === null) p.panic = Math.random() < .4 ? (Math.random() < .5 ? 'strafe' : 'jump') : 'none';   // below 30% health: 40% panic
    if (now > p.strafeAt) { p.strafe = -p.strafe; p.strafeAt = now + 500 + skill * 500 + Math.random() * 700; }
    const w0 = W(p), pref = w0.short === 'SNIPER' ? 55 : w0.short === 'ROCKET' ? 28 : 13, hurtBad = p.hp < maxHp(p) * .3 && skill > .35;   // each weapon wants a fighting distance
    const fx = dx / flat, fz = dz / flat, side = p.panic === 'strafe' || (tgt && flat < pref * 1.7) ? p.strafe : 0;
    const fwd = !tgt ? 1 : hurtBad ? -.7 : flat < 3 ? 0 : flat > pref ? 1 : skill > .5 && flat < pref * .5 ? -.5 : .2;   // close in, hold at range, back off if hurt or if good enough to know better
    let mx = fx * fwd - fz * side, mz = fz * fwd + fx * side;
    if (now < p.detourUntil) { const c = Math.cos(p.detour), s = Math.sin(p.detour); [mx, mz] = [mx * c - mz * s, mx * s + mz * c]; }   // a forced detour after being stuck
    const ml = Math.hypot(mx, mz);
    if (now > (p.progAt || 0)) {   // no progress for 1.5 s: try the other side of the obstacle
      if (p.progAt && ml > .01 && Math.hypot(p.x - p.px, p.z - p.pz) < 1.2 && (!tgt || flat > 6)) { p.side = -(p.side || 1); p.detour = p.side * 1.2; p.detourUntil = now + 1200; p.steerAt = 0; }
      p.progAt = now + 1500; p.px = p.x; p.pz = p.z;
    }
    if (ml > .01) {
      if (now > (p.steerAt || 0) || !p.hdg) { p.steerAt = now + 100; p.hdg = steer(p, mx / ml, mz / ml); }
      const [hx, hz] = p.hdg, nx = p.x + hx * BOT.speed * frameOf(p).spd * dt, nz = p.z + hz * BOT.speed * frameOf(p).spd * dt;
      if (!botBlocked(p, nx, nz)) { p.x = nx; p.z = nz; p.stuck = 0; }
      else if (!botBlocked(p, nx, p.z)) { p.x = nx; p.stuck = 0; }
      else if (!botBlocked(p, p.x, nz)) { p.z = nz; p.stuck = 0; }
      else { if (p.onGround) p.vy = BOT.jump * frameOf(p).jump; if (++p.stuck > 8) { p.side = -(p.side || 1); p.stuck = 0; p.detour = p.side * 1.3; p.detourUntil = now + 1000; p.steerAt = 0; } }   // blocked: hop, then go the other way
    }
    if (now > (p.pkAt || 0)) { p.pkAt = now + 500; takePickup(p, now, k => k.wi !== p.wi); }   // walking over a weapon: press E
    if (p.panic === 'jump' && p.onGround && Math.random() < .08) p.vy = BOT.jump * frameOf(p).jump;
    p.vy -= BOT.gravity * dt; p.y += p.vy * dt;
    const floor = surfaceY(map, p.x, p.z, p.y + BOT.step);
    if (p.vy <= 0 && p.y <= floor) { p.y = floor; p.vy = 0; p.onGround = true; } else p.onGround = false;
    p.x = r2(p.x); p.y = r2(p.y); p.z = r2(p.z);
    if (!tgt || p.reloadEnd || now < p.nextShot || now < (p.reactAt || 0) || Math.abs(wrap(wantYaw - p.yaw)) > .3) continue;
    const w = W(p), o = { x: p.x, y: p.y + BODY.eye, z: p.z }, u = { x: dx / dist, y: dy / dist, z: dz / dist };
    if (dist > w.range) continue;
    if (p.ammos[p.wi] <= 0) { if (p.reserve[p.wi] <= 0 && p.wi) p.wi = 0; else startReload(p); continue; }   // out of rockets or sniper rounds: back to the rifle
    const look = cast(p, o, u, dist); if (look.who !== tgt && look.t < dist - 1) continue;   // a wall is in the way: keep running, don't waste bullets
    if (Math.random() < (1 - skill) * .25) { p.nextShot = now + 120 + Math.random() * 300; continue; }   // weaker bots hesitate and waste time
    const e = (.025 + dist * .0012) * (1.9 - 1.5 * skill) * (p.panic ? 1.6 : 1), d = { x: u.x + (Math.random() - .5) * 2 * e, y: u.y + (Math.random() - .5) * 2 * e, z: u.z + (Math.random() - .5) * 2 * e };
    const l = Math.hypot(d.x, d.y, d.z); d.x /= l; d.y /= l; d.z /= l;                        // the random offset: bots do not have perfect aim
    p.nextShot = now + w.fireRateDelay + Math.random() * 90; p.ammos[p.wi]--;
    const hit = cast(p, o, d, w.range), t = hit.t;
    emit('fx', { a: [r2(p.x + d.x * .7), r2(o.y + d.y * .7), r2(p.z + d.z * .7)], b: [r2(o.x + d.x * t), r2(o.y + d.y * t), r2(o.z + d.z * t)], f: p.faction, s: p.prof.eq.weapon, i: p.id, e: w.splash ? w.splash.radius : 0 });
    applyHit(p, hit, o, d, w);
    if (p.alive && p.ammos[p.wi] <= 0) startReload(p);
  }
}

// ---- weapons in the world: map pickups (they return 25 s after being taken) and weapons dropped by the dead (they vanish after 30 s).
// E swaps what you hold for the pickup within reach. Everyone respawns with the assault rifle. ----
const PICKUP_RESPAWN_MS = 25000, DROP_LIFE_MS = 30000, PICKUP_RANGE = 2.5, MAX_DROPS = 24;
const pickupRows = () => pickups.filter(k => k.up).map(k => [k.id, k.wi, r2(k.x), r2(k.y), r2(k.z), k.drop ? 1 : 0]);
function finishReload(p) {   // a reload moves rounds from the spare ammo into the magazine
  const take = Math.min(W(p).magazineSize - p.ammos[p.wi], p.reserve[p.wi]);
  p.ammos[p.wi] += take; p.reserve[p.wi] -= take; p.reloadEnd = 0; emitYou(p);
}
function takePickup(p, now, want) {   // swap p's weapon for the nearest pickup in reach; want(k) lets a bot be choosy
  let best = null, bd = PICKUP_RANGE;
  for (const k of pickups) { if (!k.up || (want && !want(k))) continue; const d = Math.hypot(k.x - p.x, k.z - p.z); if (d < bd && Math.abs(k.y - p.y) < 3) { best = k; bd = d; } }
  if (!best) return false;
  const w = WEAPONS[best.wi];
  p.wi = best.wi; p.held.add(best.wi); p.ammos[best.wi] = w.magazineSize; p.reserve[best.wi] = w.maxAmmo; p.reloadEnd = 0; p.nextShot = now + SWITCH_MS;   // found weapons come fully loaded
  if (best.drop) pickups.splice(pickups.indexOf(best), 1); else { best.up = false; best.back = now + PICKUP_RESPAWN_MS; }
  emit('pk', pickupRows()); emitYou(p); notice(p, 'Picked up the ' + w.name);
  return true;
}
function dropWeapon(p) {   // the dead leave the weapon they were holding at the exact spot they died
  const k = { id: 'd' + nextId++, wi: p.wi, x: p.x, y: p.y + 1, z: p.z, up: true, drop: true, exp: Date.now() + DROP_LIFE_MS };
  pickups.push(k); const drops = pickups.filter(q => q.drop); if (drops.length > MAX_DROPS) pickups.splice(pickups.indexOf(drops[0]), 1);
  emit('pk', pickupRows());
}
function tickPickups(now) {   // map pickups come back, old drops fade away
  let changed = false;
  for (let i = pickups.length - 1; i >= 0; i--) { const k = pickups[i]; if (k.drop && now >= k.exp) { pickups.splice(i, 1); changed = true; } else if (!k.up && now >= k.back) { k.up = true; changed = true; } }
  if (changed) emit('pk', pickupRows());
}
// One shot's damage: a headshot multiplies it, and a rocket also hurts every enemy near the blast (less the further they are; never you or your team).
function applyHit(shooter, hit, o, dir, w) {
  if (hit.who) hurt(shooter, hit.who, Math.round(w.damage * (hit.head ? w.headshotMultiplier : 1) * (w.splash ? 1 - frameOf(hit.who).blast : 1)), hit.head);
  if (!w.splash) return;
  const x = o.x + dir.x * hit.t, y = o.y + dir.y * hit.t, z = o.z + dir.z * hit.t;
  for (const q of [...players.values()]) {
    if (q === shooter || q === hit.who || !q.alive || (match.mode === 'tdm' && q.faction === shooter.faction)) continue;
    const d = Math.hypot(q.x - x, q.y + 1 - y, q.z - z);
    if (d < w.splash.radius) hurt(shooter, q, Math.round(w.splash.damage * (1 - .7 * d / w.splash.radius) * (1 - frameOf(q).blast)), false);
  }
}

// ---- vehicles, turrets and the bots that drive ----
function heatOk(v, w, now) {   // the mech's miniguns: heat builds with every shot, cools 18 a second, and locks the guns for 2.5 s at 100
  if (!w.heat) return true;
  v.heat = Math.max(0, (v.heat || 0) - 18 * (now - (v.heatAt || now)) / 1000); v.heatAt = now;
  if (now < v.lockUntil) return false;
  v.heat += w.heat; if (v.heat >= 100) { v.heat = 100; v.lockUntil = now + 2500; }
  return true;
}
function tickVehicles(now) {   // roadkill: a fast car that touches an enemy on foot kills them outright, and the driver gets the kill
  for (const v of vehicles) {
    if (v.gunner) { v.gunner.x = v.x; v.gunner.z = v.z; v.gunner.y = v.y || 0; }   // the roof gunner rides along
    const D = v.driver; if (!D || (v.type !== 'car' && v.type !== 'tank') || Math.abs(v.speed) < (v.type === 'tank' ? 4 : 7)) continue;
    for (const p of [...players.values()]) {
      if (p === D || !p.alive || p.vehicle || (match.mode === 'tdm' && p.faction === D.faction)) continue;
      if (distToVehicle(v, p.x, p.z) < BODY.r && p.y < vd(v).h && p.y + BODY.h > (v.y || 0)) hurt(D, p, 9999, false, 'splat');
    }
  }
}
function makeTurrets() {   // two sentries at each base entrance, in team deathmatch only
  turrets = match.mode === 'tdm' ? (map.turrets || []).map((d, i) => ({
    id: i + 1, x: d.x, y: d.y, z: d.z, faction: d.team, yaw: 0, pitch: 0, nextShot: 0,
    sh: { id: nextId++, bot: true, name: (d.team === 'vanguard' ? 'Vanguard' : 'Horizon') + ' Sentry', faction: d.team, sock: BOT_SOCK, prof: { xp: 0, coins: 0, eq: { weapon: 'w-issue' } }, kills: 0, deaths: 0, rtt: 0, lv: 0 }
  })) : [];
}
function tickTurrets(now) {   // a turret sweeps its scanner dome; anything hostile inside it (on foot or driving) is tracked and shot
  for (const t of turrets) {
    let tgt = null, best = TURRET.radius;
    for (const q of players.values()) { if (!q.alive || q.faction === t.faction) continue; const d = Math.hypot(q.x - t.x, q.y + 1 - t.y, q.z - t.z); if (d < best) { best = d; tgt = q; } }
    if (!tgt) continue;
    const dx = tgt.x - t.x, dy = tgt.y + 1.2 - (t.y + .6), dz = tgt.z - t.z, flat = Math.hypot(dx, dz) || 1, dist = Math.hypot(dx, dy, dz) || 1, want = Math.atan2(-dx, -dz);
    t.yaw = r3(wrap(t.yaw + clamp(wrap(want - t.yaw), -.22, .22))); t.pitch = r3(clamp(t.pitch + clamp(Math.atan2(dy, flat) - t.pitch, -.15, .15), -.4, 1.2));
    if (now < t.nextShot || Math.abs(wrap(want - t.yaw)) > .12) continue;
    const o = { x: t.x, y: t.y + .6, z: t.z }, u = { x: dx / dist, y: dy / dist, z: dz / dist };
    const look = cast(t.sh, o, u, dist); if (look.who !== tgt && look.t < dist - 1) continue;   // a wall in the way
    const e = .02 + dist * .0008, d = { x: u.x + (Math.random() - .5) * 2 * e, y: u.y + (Math.random() - .5) * 2 * e, z: u.z + (Math.random() - .5) * 2 * e }, l = Math.hypot(d.x, d.y, d.z);
    d.x /= l; d.y /= l; d.z /= l; t.nextShot = now + TURRET.fireRateDelay;
    const hit = cast(t.sh, o, d, TURRET.range), tt = hit.t;
    emit('fx', { a: [r2(o.x + d.x * .8), r2(o.y + d.y * .8), r2(o.z + d.z * .8)], b: [r2(o.x + d.x * tt), r2(o.y + d.y * tt), r2(o.z + d.z * tt)], f: t.faction, s: 'w-issue', i: 0, e: 0 });
    applyHit(t.sh, hit, o, d, TURRET);
  }
}
function vehBlocked(v, x, z) {   // a ground vehicle or mech cannot drive through walls or off the map
  const r = vd(v).hx + .4;
  if (Math.abs(x) > map.half - 3 || Math.abs(z) > map.half - 3) return true;
  for (const k of map.blocks) if ((k.y || 0) < 2 && (k.y || 0) + k.h > .3 && Math.abs(x - k.x) < k.hx + r && Math.abs(z - k.z) < k.hz + r) return true;
  return false;
}
// A bot at the wheel: cars charge the nearest enemy (the roadkill check does the rest), helicopters climb to 22 m and rocket from range, mechs walk up and use their miniguns.
function botDrive(p, now, dt) {
  const v = vehicles.find(x => x.id === p.vehicle); if (!v) { p.vehicle = 0; return; }
  let tgt = null, best = Infinity;
  for (const q of players.values()) { if (q === p || !q.alive || q.vehicle === p.vehicle || (match.mode === 'tdm' && q.faction === p.faction)) continue; const d = Math.hypot(q.x - v.x, q.z - v.z); if (d < best) { best = d; tgt = q; } }
  if (!tgt || now - p.drove > 45000 || p.stuck > 40) { leaveVehicle(p, true); p.stuck = 0; p.boardAt = now + 8000; return; }   // nobody left to hunt, or stuck: get out
  const dx = tgt.x - v.x, dz = tgt.z - v.z, flat = Math.hypot(dx, dz) || 1, want = Math.atan2(-dx, -dz), T = vd(v), w = VWEAPONS[v.type];
  v.yaw = r3(wrap(v.yaw + clamp(wrap(want - v.yaw), -.08, .08)));
  const sp = v.type === 'car' ? 18 : v.type === 'tank' ? (flat < 30 ? 0 : 7.5) : v.type === 'heli' ? (flat < 70 ? 0 : 14) : (flat < 40 ? 0 : 4.2);
  const nx = v.x - Math.sin(v.yaw) * sp * dt, nz = v.z - Math.cos(v.yaw) * sp * dt;
  if (v.type === 'heli' || !vehBlocked(v, nx, nz)) { v.x = nx; v.z = nz; p.stuck = 0; } else { v.yaw = r3(wrap(v.yaw + .5)); p.stuck++; }   // blocked: swing away
  if (v.type === 'heli') v.y = Math.min(22, (v.y || 0) + 6 * dt);
  const lim = map.half - T.hx; v.x = r2(clamp(v.x, -lim, lim)); v.z = r2(clamp(v.z, -lim, lim)); v.speed = sp; v.dirty = true;
  p.x = v.x; p.y = v.y || 0; p.z = v.z; p.yaw = v.yaw;
  if (!w || flat > w.range * .9 || Math.abs(wrap(want - v.yaw)) > .25 || now < p.nextShot || (v.type === 'heli' && v.y < 15)) return;
  const side = v.type === 'mech' ? (now / 45 & 1 ? 1 : -1) * 1.1 : 0, c = Math.cos(v.yaw), s = Math.sin(v.yaw);
  const o = { x: v.x - s * 2.2 + c * side, y: (v.y || 0) + (v.type === 'mech' ? 4.2 : v.type === 'tank' ? 2 : 1.2), z: v.z - c * 2.2 - s * side }, dy = tgt.y + 1.2 - o.y, dist = Math.hypot(dx, dy, dz) || 1;
  if (!heatOk(v, w, now)) return;
  const e = .03 + dist * .0012, d = { x: dx / dist + (Math.random() - .5) * 2 * e, y: dy / dist + (Math.random() - .5) * 2 * e, z: dz / dist + (Math.random() - .5) * 2 * e }, l = Math.hypot(d.x, d.y, d.z);
  d.x /= l; d.y /= l; d.z /= l; p.nextShot = now + w.fireRateDelay + Math.random() * 40;
  const hit = cast(p, o, d, w.range), t = hit.t;
  emit('fx', { a: [r2(o.x), r2(o.y), r2(o.z)], b: [r2(o.x + d.x * t), r2(o.y + d.y * t), r2(o.z + d.z * t)], f: p.faction, s: p.prof.eq.weapon, i: p.id, e: w.splash ? w.splash.radius : 0 });
  applyHit(p, hit, o, d, w);
}

// ---- rooms and matchmaking ----
// A "room" is one isolated match, named like Server-US-1. Players are put in a Socket.io room of that name, so every emit() below reaches
// only that room. Rooms are made on demand and closed after a minute with no humans in them.
const rooms = new Map(); let roomSeq = 0;
const emit = (...a) => io.to(cur.id).emit(...a);   // to everyone in the current room
const humansIn = r => { let n = 0; for (const p of r.players.values()) if (!p.bot) n++; return n; };
function loadRoom(r) { cur = r; players = r.players; match = r.match; map = r.map; vehicles = r.vehicles; tick = r.tick; nextTimer = r.nextTimer; spawnHeld = r.spawnHeld; pickups = r.pickups; turrets = r.turrets; }
function inRoom(room, fn) {   // run fn with the shared variables pointing at this room, then save them back
  const prev = cur; loadRoom(room);
  try { return fn(); } finally { room.map = map; room.vehicles = vehicles; room.tick = tick; room.nextTimer = nextTimer; room.pickups = pickups; room.turrets = turrets; if (prev) loadRoom(prev); }
}
function createRoom() {
  const room = { id: 'Server-' + REGION + '-' + (++roomSeq), players: new Map(), match: { mode: 'tdm', state: 'live', team: { vanguard: 0, horizon: 0 } }, map: MAPS.field, vehicles: [], tick: 0, nextTimer: null, spawnHeld: new Map(), pickups: [], turrets: [], emptySince: 0 };
  rooms.set(room.id, room);
  inRoom(room, () => startMatch(MODE === 'rotate' ? 'tdm' : MODE, MAP_ENV === 'rotate' ? 'frontier' : MAP_ENV));   // new rooms open on Twin Citadels, then the maps rotate
  console.log('opened ' + room.id + ' (' + room.match.mode + ' on ' + room.map.id + '), ' + rooms.size + ' rooms');
  return room;
}
// Matchmaking, run for every player who clicks Play: the room with the most real humans that still has a free human slot (bots give their
// slots up), else a brand new room, which fills itself with bots. null means the process is at MAX_ROOMS and every room is full.
function matchmake() {
  const open = [...rooms.values()].map(r => ({ r, h: humansIn(r) })).filter(x => x.h < MAX_PLAYERS).sort((a, b) => b.h - a.h);
  return open.length ? open[0].r : rooms.size < MAX_ROOMS ? createRoom() : null;
}

// ---- connections ----
io.on('connection', socket => {
  const room = matchmake();
  if (!room) { socket.emit('full'); socket.disconnect(true); return; }
  inRoom(room, () => connect(socket, room));
});
function connect(socket, room) {
  if (players.size >= MAX_PLAYERS && !kickBot()) { socket.emit('full'); socket.disconnect(true); return; }   // a full room of bots makes space for a person
  socket.join(room.id);
  const id = nextId++;
  const auth = (socket.handshake && socket.handshake.auth) || {};
  const token = typeof auth.token === 'string' && /^[a-f0-9]{32}$/.test(auth.token) ? auth.token : crypto.randomBytes(16).toString('hex');
  let prof = store.get(token);
  if (!prof) { prof = adopt(token, auth.save); if (prof) store.set(token, prof); else prof = newProfile(); }   // from the browser's signed backup, or brand new
  const me = {
    id, room, sock: socket, token, prof, shopAt: 0, name: 'Pilot ' + id, faction: pickFaction(), x: 0, y: 0, z: 0, yaw: 0, pitch: 0, last: 0, lastVeh: 0, useAt: 0,
    hp: HP, alive: true, kills: 0, deaths: 0, ammos: WEAPONS.map(w => w.magazineSize), reserve: WEAPONS.map(w => w.maxAmmo), held: new Set(), wi: 0, vehicle: 0, reloadEnd: 0, nextShot: 0, respawnAt: 0, epoch: 0, rtt: 100, hist: [], nameAt: 0
  };
  const sp = pickSpawn(me); Object.assign(me, { x: sp.x, y: sp.y, z: sp.z, yaw: sp.yaw });   // a safe point from the spawn matrix
  players.set(socket.id, me); me.hp = maxHp(me);
  const on = (ev, fn) => socket.on(ev, (...a) => inRoom(room, () => fn(...a)));   // every event runs inside this player's room
  socket.emit('welcome', {
    ...pub(me), room: room.id, hp: me.hp, ammos: me.ammos, reserve: me.reserve, wi: me.wi, pickups: pickupRows(), weapons: WEAPONS, map: clientMap(map), vehicles: vehRows(), token, profile: profileView(me), skins: SKINS,
    match: matchInfo(), players: [...players.values()].filter(p => p !== me).map(pub)
  });
  socket.to(room.id).emit('join', pub(me));
  console.log(`+ ${me.name} (${me.faction}) joined ${room.id}, ${players.size} there, ${match.mode} on ${map.id}`);

  on('state', d => {
    const now = Date.now();
    if (!d || !me.alive || me.vehicle || d.e !== me.epoch || now - me.last < 15) return;     // dead, driving, stale (before a respawn) or flooding
    if (![d.x, d.y, d.z, d.yaw, d.pitch].every(n => typeof n === 'number' && Number.isFinite(n))) return;
    me.last = now;
    const b = map.bounds, pad = b.edge === 'void' ? 12 : 0;   // wall maps stop you at the box; a void map lets you step past it, and that is a death
    me.x = r2(clamp(d.x, b.min[0] - pad, b.max[0] + pad)); me.y = r2(clamp(d.y, b.min[1] - 12, b.max[1])); me.z = r2(clamp(d.z, b.min[2] - pad, b.max[2] + pad));
    me.yaw = r3(clamp(d.yaw, -Math.PI, Math.PI)); me.pitch = r3(clamp(d.pitch, -Math.PI / 2, Math.PI / 2));
  });

  on('shoot', d => {
    const now = Date.now(), veh = me.vehicle ? vehicles.find(x => x.id === me.vehicle) : null, w = veh ? VWEAPONS[me.seat ? 'cargun' : veh.type] : W(me);
    if (!w || !d || !me.alive || match.state !== 'live' || (!veh && me.reloadEnd) || now < me.nextShot) return;   // a car has no gun; fire rate and reload are enforced here   // fire rate, reload and driving are enforced here
    if (!['ox', 'oy', 'oz', 'dx', 'dy', 'dz'].every(k => typeof d[k] === 'number' && Number.isFinite(d[k]))) return;
    const len = Math.hypot(d.dx, d.dy, d.dz);
    if (len < .5) return;
    const o = { x: d.ox, y: d.oy, z: d.oz }, dir = { x: d.dx / len, y: d.dy / len, z: d.dz / len };
    if (Math.hypot(o.x - me.x, o.y - (me.y + (veh ? vd(veh).h * .7 : BODY.eye)), o.z - me.z) > (veh ? 9 : 6)) return;   // the ray must start near the shooter (or the vehicle's guns)
    if (veh) { if (!heatOk(veh, w, now)) return; me.nextShot = now + w.fireRateDelay * .8; }   // vehicle guns have no ammo; the mech overheats instead
    else { if (me.ammos[me.wi] <= 0) { startReload(me); return; } me.nextShot = now + w.fireRateDelay * .8; me.ammos[me.wi]--; }
    const hit = cast(me, o, dir, w.range), t = hit.t;
    socket.to(room.id).emit('fx', {                                                    // let everyone else see the tracer
      a: veh ? [r2(o.x), r2(o.y), r2(o.z)] : [r2(me.x + dir.x * .7), r2(me.y + BODY.eye + dir.y * .7), r2(me.z + dir.z * .7)],
      b: [r2(o.x + dir.x * t), r2(o.y + dir.y * t), r2(o.z + dir.z * t)], f: me.faction, s: profOf(me).eq.weapon, i: me.id, e: w.splash ? w.splash.radius : 0
    });
    applyHit(me, hit, o, dir, w);
    if (!veh && me.alive && me.ammos[me.wi] <= 0) startReload(me);
  });

  on('reload', () => { if (me.alive && !me.vehicle && match.state === 'live') startReload(me); });

  on('switch', i => {                      // changing weapon cancels a reload and costs a short draw time
    if (!Number.isInteger(i) || i < 0 || i >= WEAPONS.length || i === me.wi || !me.alive || me.vehicle) return;
    if (lvOf(me) < WEAPONS[i].unlockLevel && !me.held.has(i)) { emitYou(me); return notice(me, WEAPONS[i].name + ' unlocks at level ' + WEAPONS[i].unlockLevel + ', or find one on the map'); }
    me.wi = i; me.reloadEnd = 0; me.nextShot = Math.max(me.nextShot, Date.now() + SWITCH_MS);
    emitYou(me);
  });

  on('use', () => {                        // the E key
    const now = Date.now();
    if (!me.alive || match.state !== 'live' || now - me.useAt < 250) return;
    me.useAt = now;
    if (me.vehicle) { leaveVehicle(me, true); return; }
    if (takePickup(me, now)) return;   // a weapon within reach comes before a vehicle
    let best = null, bd = VEH.useRange, gun = false;
    for (const v of vehicles) {   // a free seat, a pillar gun, or the roof gun of a friendly car that already has a driver
      const open = !v.driver, roof = v.type === 'car' && v.driver && !v.gunner && (match.mode !== 'tdm' || v.driver.faction === me.faction);
      if (!(open || roof) || (v.type !== 'turret' && Math.abs((v.y || 0) - me.y) > 3)) continue;
      const d = distToVehicle(v, me.x, me.z); if (d <= bd) { best = v; bd = d; gun = !open; }
    }
    if (!best) return;
    if (gun) { best.gunner = me; me.seat = 'g'; } else best.driver = me;
    me.vehicle = best.id; me.reloadEnd = 0;
    if (best.type === 'turret') { me.x = best.x; me.z = best.z; me.y = best.sy; }
    socket.emit('drive', { vid: best.id, x: best.x, z: best.z, yaw: best.yaw, g: gun ? 1 : 0 });
    emit('vehicles', vehRows());
  });

  on('veh', d => {                         // the driver reports the vehicle's pose
    const v = me.vehicle && vehicles.find(x => x.id === me.vehicle), now = Date.now();
    if (!v || !d || !me.alive || me.seat || now - me.lastVeh < 15) return;
    if (![d.x, d.z, d.yaw, d.speed].every(n => typeof n === 'number' && Number.isFinite(n))) return;
    me.lastVeh = now;
    if (v.type === 'turret') { v.yaw = r3(wrap(d.yaw)); me.x = v.x; me.z = v.z; me.y = v.sy; v.dirty = true; return; }   // a pillar gun only turns
    const T = vd(v), lim = map.half - T.hx;
    v.x = r2(clamp(d.x, -lim, lim)); v.z = r2(clamp(d.z, -lim, lim)); v.yaw = r3(wrap(d.yaw)); v.speed = r2(clamp(d.speed, -T.maxReverse, T.maxSpeed));
    v.y = v.type === 'heli' && Number.isFinite(d.y) ? r2(clamp(d.y, 0, map.bounds.max[1] - 4)) : 0;   // only helicopters leave the ground
    me.x = v.x; me.z = v.z; me.y = v.y; v.dirty = true;
  });

  on('melee', d => {   // F: a strike at arm's length. The Raider frame hits hardest. The server uses its own idea of where the eye is.
    const now = Date.now();
    if (!d || !me.alive || me.vehicle || match.state !== 'live' || now < (me.meleeAt || 0)) return;
    if (![d.dx, d.dy, d.dz].every(n => typeof n === 'number' && Number.isFinite(n))) return;
    const len = Math.hypot(d.dx, d.dy, d.dz); if (len < .5) return; me.meleeAt = now + 650;
    const hit = cast(me, { x: me.x, y: me.y + BODY.eye, z: me.z }, { x: d.dx / len, y: d.dy / len, z: d.dz / len }, MELEE_RANGE);
    if (hit.who && !(match.mode === 'tdm' && hit.who.faction === me.faction)) hurt(me, hit.who, Math.round(MELEE_DMG * frameOf(me).melee), !!hit.head, 'melee');
  });

  on('buy', id => {                        // spend coins on a skin; buying also equips it
    const s = skinById.get(id), pr = profOf(me), now = Date.now();
    if (!s || now - me.shopAt < 200) return; me.shopAt = now;
    if (pr.owned.includes(id)) return notice(me, 'You already own that');
    if (levelInfo(pr.xp).level < s.level) return notice(me, 'Reach level ' + s.level + ' to unlock this');
    if (pr.coins < s.price) return notice(me, s.name + ' costs ' + s.price + ' coins. You have ' + pr.coins + '.', { code: 'coins' });   // the client shows its Insufficient Coins popup
    pr.coins -= s.price; pr.owned.push(id);
    equip(me, s);
  });

  on('equip', id => {
    const s = skinById.get(id), now = Date.now();
    if (!s || now - me.shopAt < 200) return; me.shopAt = now;
    if (!profOf(me).owned.includes(id)) return notice(me, 'Unlock that skin first');
    equip(me, s);
  });

  on('name', n => {
    const now = Date.now(), nm = cleanName(n, me.id);
    if (now - me.nameAt < 1000 || nm === me.name) return;
    if (nameTaken(nm, me)) return notice(me, 'That name is already taken in this room');   // no two players, human or bot, share a name
    me.nameAt = now; me.name = nm;
    emit('rename', { id: me.id, name: nm });
  });

  on('disconnect', () => {
    if (me.vehicle) leaveVehicle(me, false);
    players.delete(socket.id);
    emit('leave', me.id);
    console.log(`- ${me.name} left ${room.id}, ${players.size} there`);
  });
}

// The heartbeat: 20 times a second. Records history for lag compensation, finishes reloads, respawns the dead,
// measures each player's round-trip time, and sends everybody one snapshot (plus vehicle poses when one moved).
function tickRoom() {
  const now = Date.now(); tick++;
  for (const p of players.values()) {
    if (p.alive) { p.hist.push({ t: now, x: p.x, y: p.y, z: p.z }); if (p.hist.length > 25) p.hist.shift(); }
    else if (match.state === 'live' && now >= p.respawnAt) respawn(p);
    if (p.alive && !p.vehicle && match.state === 'live') { const why = oobReason(p); if (why) eliminate(p, why); }   // out of bounds or in a kill zone
    if (p.reloadEnd && now >= p.reloadEnd) finishReload(p);
    if (tick % (TICK_HZ * 2) === 0) { const t0 = now; p.sock.emit('lag', () => { p.rtt = Math.min(1000, Date.now() - t0); }); }
  }
  botTick(now); tickVehicles(now); tickTurrets(now); tickPickups(now); if (tick % TICK_HZ === 0) balanceBots();   // bots think, and empty slots are filled once a second
  if (!players.size) return;
  const list = [...players.values()].map(p => [p.id, p.x, p.y, p.z, p.yaw, p.pitch, p.alive ? 1 : 0, p.vehicle, p.wi]);
  const moved = vehicles.some(v => v.dirty), rows = moved ? vehRows() : null, trRows = turrets.length ? turrets.map(t => [t.id, t.yaw, t.pitch]) : null;
  vehicles.forEach(v => { v.dirty = false; });
  for (const p of players.values()) if (!p.bot) { p.sock.volatile.emit('snapshot', list); if (moved) p.sock.volatile.emit('vehicles', rows); if (trRows) p.sock.volatile.emit('tr', trRows); }
}
setInterval(() => {   // every room ticks on its own, bots included; a room with no humans for a minute is closed (one stays open)
  const now = Date.now();
  for (const room of [...rooms.values()]) {
    inRoom(room, tickRoom);
    if (humansIn(room)) room.emptySince = 0;
    else if (!room.emptySince) room.emptySince = now;
    else if (now - room.emptySince > ROOM_IDLE_MS && rooms.size > 1) { clearTimeout(room.nextTimer); rooms.delete(room.id); console.log('closed ' + room.id + ', ' + rooms.size + ' rooms'); }
  }
}, 1000 / TICK_HZ);

for (const m of Object.values(MAPS)) { const bad = validateMap(m); if (bad.length) console.error('MAP PROBLEM in ' + m.id + ':\n  ' + bad.join('\n  ')); }
createRoom();   // keep one room open so the first player joins at once
for (const sig of ['SIGTERM', 'SIGINT']) process.on(sig, () => { store.flush(); process.exit(0); });   // save on a clean shutdown
server.listen(PORT, () => console.log(`Riftline server listening on port ${PORT}, mode ${MODE}, map ${MAP_ENV}`));

if (require.main !== module) module.exports = { MAPS, validateMap, surfaceY, rayRamp, rayBox, rampY, clientMap, rooms, inRoom, createRoom, cast, applyHit, hurt, takePickup, WEAPONS, tickVehicles, tickTurrets, heatOk, VWEAPONS };   // lets the tests reach the geometry helpers
