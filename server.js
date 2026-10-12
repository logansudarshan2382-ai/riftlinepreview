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
 *                    profile {xp,level,into,need,credits,owned,eq,save,gain?}   your progress, after every change
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
const HP = 100, RESPAWN_MS = 3000, INTERMISSION_MS = 8000, SWITCH_MS = 350;
const LIMIT = { tdm: Number(process.env.TDM_LIMIT) || 20, ffa: Number(process.env.FFA_LIMIT) || 10 };   // kills needed to win
const BODY = { r: .4, h: 1.8, eye: 1.62 };
const VEH = { hx: 1.3, hz: 2.5, h: 1.6, maxSpeed: 16, maxReverse: 6, useRange: 1.8 };

// ---- progression: XP, levels, credits and skins, saved per player ----
const XP_PER_KILL = 100, CREDITS_PER_KILL = 50, WIN_CREDITS = 150, LEVEL_UP_CREDITS = 100, MAX_PROFILES = 5000;
const xpToNext = level => 200 + 100 * level;   // level 1 -> 2 takes 300 XP, then 400, 500 ...
function levelInfo(xp) { let level = 1, rest = xp; while (rest >= xpToNext(level)) { rest -= xpToNext(level); level++; } return { level, into: rest, need: xpToNext(level) }; }

// Cosmetics only. Body skins repaint the capsule, but the faction colour still glows through so teams stay readable.
// Weapon skins repaint the gun and can recolour its tracer. color: null means "use the faction colour".
const SKINS = [
  { id: 'issue',    slot: 'body',   name: 'Faction issue',   price: 0,    level: 1, color: null,     metal: .25, rough: .45, glow: .3 },
  { id: 'carbon',   slot: 'body',   name: 'Carbon',          price: 300,  level: 1, color: 0x1a1c21, metal: .7,  rough: .35, glow: .45 },
  { id: 'chrome',   slot: 'body',   name: 'Neon Chrome',     price: 800,  level: 3, color: 0xdff3ff, metal: 1,   rough: .12, glow: .3 },
  { id: 'ember',    slot: 'body',   name: 'Ember',           price: 1200, level: 5, color: 0x8a2a0a, metal: .5,  rough: .4,  glow: .6 },
  { id: 'void',     slot: 'body',   name: 'Void Glass',      price: 2000, level: 8, color: 0x2a1a55, metal: .9,  rough: .1,  glow: .55 },
  { id: 'w-issue',  slot: 'weapon', name: 'Standard finish', price: 0,    level: 1, color: 0x3a3f4d, metal: .6,  rough: .45, beam: null },
  { id: 'w-carbon', slot: 'weapon', name: 'Carbon',          price: 250,  level: 1, color: 0x15161a, metal: .7,  rough: .35, beam: null },
  { id: 'w-chrome', slot: 'weapon', name: 'Neon Chrome',     price: 700,  level: 3, color: 0xdff3ff, metal: 1,   rough: .12, beam: 0x9bf5ff },
  { id: 'w-ember',  slot: 'weapon', name: 'Ember',           price: 1000, level: 5, color: 0x8a2a0a, metal: .5,  rough: .4,  beam: 0xff8a3a }
];
const skinById = new Map(SKINS.map(s => [s.id, s]));
const newProfile = () => ({ xp: 0, credits: 0, kills: 0, owned: ['issue', 'w-issue'], eq: { body: 'issue', weapon: 'w-issue' }, rev: 0, seen: Date.now() });

// The "mock database": every profile in one JSON file, keyed by a secret token that the player's browser keeps.
// Render's free plan wipes local files on every restart or sleep, so each player's browser also holds a signed backup
// (see sign/adopt below). The signature uses SAVE_SECRET, so a player can't edit their own XP or credits.
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const SAVE_SECRET = process.env.SAVE_SECRET || crypto.randomBytes(32).toString('hex');
if (!process.env.SAVE_SECRET) console.warn("SAVE_SECRET is not set: players' backup saves will stop working whenever this server restarts.");
class Store {
  constructor(file) {
    this.file = file; this.timer = null; this.data = {};
    try {
      const d = JSON.parse(fs.readFileSync(file, 'utf8'));
      for (const k of Object.keys(d)) if (/^[a-f0-9]{32}$/.test(k) && d[k] && Array.isArray(d[k].owned) && d[k].eq) this.data[k] = d[k];
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
  const body = Buffer.from(JSON.stringify({ t: token, xp: p.xp, credits: p.credits, kills: p.kills, owned: p.owned, eq: p.eq })).toString('base64url');
  return body + '.' + mac(body);
}
function adopt(token, save) {   // restore a profile from a signed backup, if the signature is ours and it belongs to this token
  if (typeof save !== 'string' || save.length > 4000) return null;
  const [body, sig] = save.split('.');
  if (!body || !sig || !safeEqual(sig, mac(body))) return null;
  try {
    const d = JSON.parse(Buffer.from(body, 'base64url').toString());
    if (d.t !== token) return null;
    const owned = [...new Set(['issue', 'w-issue', ...(Array.isArray(d.owned) ? d.owned : []).filter(id => skinById.has(id))])];
    const worn = (id, slot, def) => (owned.includes(id) && skinById.get(id).slot === slot ? id : def);
    const n = v => Math.max(0, Math.floor(Number(v)) || 0);
    return { xp: n(d.xp), credits: n(d.credits), kills: n(d.kills), owned, eq: { body: worn(d.eq && d.eq.body, 'body', 'issue'), weapon: worn(d.eq && d.eq.weapon, 'weapon', 'w-issue') }, rev: 1, seen: Date.now() };
  } catch (e) { return null; }
}

// ---- weapons: the first one is what everybody spawns with. Add a line here and it appears in the game. ----
const WEAPONS = [
  { name: 'Rift pistol',   short: 'PISTOL', damage: 20, fireRate: 6,   mag: 12, reload: 1.5, range: 150, auto: false, len: .6 },
  { name: 'Assault rifle', short: 'RIFLE',  damage: 12, fireRate: 11,  mag: 30, reload: 2.0, range: 120, auto: true, len: 1 },
  { name: 'Sniper rifle',  short: 'SNIPER', damage: 75, fireRate: .9,  mag: 5,  reload: 2.6, range: 300, auto: false, len: 1.5 }
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
    id: 'field', name: 'Pillar Fields', half: 60, sky: 0x0f1530, fog: [40, 140], sun: true, ceiling: 0, lights: [], tint: 0x8d9bc8, accent: 0x7aa2ff, stars: false,
    ground: 0, bounds: { min: [-60, -2, -60], max: [60, 40, 60], edge: 'wall' }, killZones: [], ramps: [],
    blocks: [B(-14, -14, 1, 1, 7, 'pillar'), B(14, -14, 1, 1, 7, 'pillar'), B(-14, 14, 1, 1, 7, 'pillar'), B(14, 14, 1, 1, 7, 'pillar'),
             B(-32, -8, 1, 1, 7, 'pillar'), B(32, -8, 1, 1, 7, 'pillar'), B(-32, 8, 1, 1, 7, 'pillar'), B(32, 8, 1, 1, 7, 'pillar'),
             B(0, -6, 2, .6, 1, 'crate'), B(-8, 4, .6, 2, 1, 'crate'), B(8, 4, .6, 2, 1, 'crate'), B(0, 22, 3, .6, 1.2, 'crate'),
             B(-26, 26, 5, 4, 5, 'building'), B(26, -26, 5, 4, 5, 'building')],
    spawns: { ffa: spawnRing(46, 16), vanguard: spawnRow(-35, -46, 35, -46, 8), horizon: spawnRow(-35, 46, 35, 46, 8) },
    vehicles: [{ x: 0, z: 12, yaw: 0 }]
  },
  arena: {   // a tight indoor arena: metal walls, doorways, a central block and a ceiling
    id: 'arena', name: 'Close Quarters', half: 24, sky: 0x07090f, fog: [10, 55], sun: false, ceiling: 6, lights: [[0, 5, -14], [0, 5, 14]], tint: 0xc9a98a, accent: 0xff9a4d, stars: false,
    ground: 0, bounds: { min: [-24, -2, -24], max: [24, 8, 24], edge: 'wall' }, killZones: [], ramps: [],
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
    id: 'station', name: 'Orbital Station', half: 30, sky: 0x03040a, fog: [70, 280], sun: true, ceiling: 0, lights: [], tint: 0xb4bdd6, accent: 0xb48cff, stars: true, hull: { top: 44, bottom: 14, depth: 20 },
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

const players = new Map();   // socket.id -> player
const match = { mode: 'tdm', state: 'live', team: { vanguard: 0, horizon: 0 } };
let map = MAPS.field, vehicles = [], nextId = 1, spawnIx = 0, tick = 0, nextTimer = null;

const app = express();
if (process.env.SITE_DIR) app.use(express.static(path.resolve(process.env.SITE_DIR)));   // optional: serve the arcade locally too
app.get('/health', (req, res) => res.json({ ok: true, players: players.size, mode: match.mode, map: map.id }));

const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: (origin, cb) => cb(null, !origin || ORIGINS.includes(origin) || /^http:\/\/(localhost|127\.0\.0\.1)(:\d+)?$/.test(origin)) },
  maxHttpBufferSize: 1e4
});

const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));
const wrap = a => ((a + Math.PI) % (2 * Math.PI) + 2 * Math.PI) % (2 * Math.PI) - Math.PI;
const r2 = v => Math.round(v * 100) / 100, r3 = v => Math.round(v * 1000) / 1000;
const W = p => WEAPONS[p.wi];
const pub = p => ({ id: p.id, name: p.name, faction: p.faction, kills: p.kills, deaths: p.deaths, alive: p.alive, x: p.x, y: p.y, z: p.z, yaw: p.yaw, pitch: p.pitch, skin: { body: profOf(p).eq.body, weapon: profOf(p).eq.weapon } });
const matchInfo = () => ({ mode: match.mode, limit: LIMIT[match.mode], state: match.state, team: match.team, map: map.name });
const sendScores = () => io.emit('scores', { t: match.team, p: [...players.values()].map(p => [p.id, p.kills, p.deaths]) });
const vehRows = () => vehicles.map(v => [v.id, r2(v.x), r2(v.z), r3(v.yaw), v.driver ? v.driver.id : 0]);
function profileView(p) {
  const pr = profOf(p), lv = levelInfo(pr.xp);
  return { xp: pr.xp, level: lv.level, into: lv.into, need: lv.need, credits: pr.credits, kills: pr.kills, owned: pr.owned, eq: pr.eq, save: sign(p.token, pr) };
}
const notice = (p, text) => p.sock.emit('notice', { text });
function grant(p, xp, credits, why) {   // XP and credits go to the player's saved profile; a level-up pays a bonus
  const pr = profOf(p), before = levelInfo(pr.xp).level;
  pr.xp += xp; pr.credits += credits; if (why === 'kill') pr.kills++;
  const up = levelInfo(pr.xp).level - before, bonus = up > 0 ? LEVEL_UP_CREDITS * up : 0;
  pr.credits += bonus; pr.rev++; store.set(p.token, pr);
  p.sock.emit('profile', { ...profileView(p), gain: { xp, credits: credits + bonus, why }, levelUp: up > 0 });
}
function equip(p, s) {   // wear a skin and tell everyone, so they see it too
  const pr = profOf(p); pr.eq[s.slot] = s.id; pr.rev++; store.set(p.token, pr);
  p.sock.emit('profile', profileView(p));
  io.emit('skin', { id: p.id, body: pr.eq.body, weapon: pr.eq.weapon });
}
const emitYou = p => p.sock.emit('you', { hp: p.hp, ammos: p.ammos, wi: p.wi, reloading: !!p.reloadEnd });
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
const spawnHeld = new Map();   // spawn point -> when it was last used
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
  Object.assign(p, { x: sp.x, y: sp.y, z: sp.z, yaw: sp.yaw, pitch: 0, hp: HP, alive: true, ammos: WEAPONS.map(w => w.mag), reloadEnd: 0, nextShot: 0, vehicle: 0, epoch: p.epoch + 1, hist: [] });
  p.sock.emit('respawn', { x: sp.x, y: sp.y, z: sp.z, yaw: sp.yaw, hp: HP, ammos: p.ammos, wi: p.wi, e: p.epoch });   // e: old position updates still in flight are ignored
}

function startReload(p) {
  if (p.reloadEnd || p.ammos[p.wi] >= W(p).mag) return;
  p.reloadEnd = Date.now() + W(p).reload * 1000;
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
  return rayBox({ x: dx * c - dz * s, y: o.y, z: dx * s + dz * c }, { x: d.x * c - d.z * s, y: d.y, z: d.x * s + d.z * c }, -VEH.hx, 0, -VEH.hz, VEH.hx, VEH.h, VEH.hz);
}
function distToVehicle(v, x, z) {   // ground-plane distance from a point to the vehicle's body (0 = touching)
  const c = Math.cos(v.yaw), s = Math.sin(v.yaw), dx = x - v.x, dz = z - v.z;
  return Math.hypot(Math.max(Math.abs(dx * c - dz * s) - VEH.hx, 0), Math.max(Math.abs(dx * s + dz * c) - VEH.hz, 0));
}
function exitSpot(v) {   // first free spot beside the vehicle: right, left, behind, in front. It must be on a floor, clear of walls and kill zones
  const c = Math.cos(v.yaw), s = Math.sin(v.yaw), lim = map.half - BODY.r;
  const solid = [...map.blocks.filter(groundBlock), ...map.ramps, ...map.killZones.map(k => ({ x: (k.min[0] + k.max[0]) / 2, z: (k.min[2] + k.max[2]) / 2, hx: (k.max[0] - k.min[0]) / 2, hz: (k.max[2] - k.min[2]) / 2 }))];
  for (const [lx, lz] of [[VEH.hx + 1, 0], [-VEH.hx - 1, 0], [0, VEH.hz + 1], [0, -VEH.hz - 1]]) {
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
    const t = rayVehicle(o, d, v);
    if (t !== null && t < best.t) best = { t, who: v.driver && v.driver !== shooter && !friend(v.driver) ? v.driver : null };
  }
  const when = Date.now() - Math.min(400, shooter.rtt + 100);   // round trip plus the 100 ms clients draw others in the past
  for (const p of players.values()) {
    if (p === shooter || !p.alive || p.vehicle || friend(p)) continue;   // no friendly fire; drivers are covered by the vehicle above
    const q = posAt(p, when);
    const t = rayBox(o, d, q.x - BODY.r, q.y, q.z - BODY.r, q.x + BODY.r, q.y + BODY.h, q.z + BODY.r);
    if (t !== null && t < best.t) best = { t, who: p };
  }
  return best;
}

function leaveVehicle(p, notify) {
  const v = vehicles.find(x => x.id === p.vehicle);
  p.vehicle = 0;
  if (!v) return;
  v.driver = null; v.speed = 0;
  if (notify) { const s = exitSpot(v); p.x = s.x; p.z = s.z; p.y = 0; p.sock.emit('undrive', { x: s.x, z: s.z }); }
  io.emit('vehicles', vehRows());
}

function hurt(shooter, target, dmg) {
  target.hp -= dmg;
  const dead = target.hp <= 0;
  shooter.sock.emit('hit', { kill: dead });
  if (!dead) { emitYou(target); return; }
  target.hp = 0; target.alive = false; target.deaths++; shooter.kills++; target.respawnAt = Date.now() + RESPAWN_MS; target.reloadEnd = 0;
  if (target.vehicle) leaveVehicle(target, false);
  if (match.mode === 'tdm') match.team[shooter.faction]++;
  grant(shooter, XP_PER_KILL, CREDITS_PER_KILL, 'kill');
  emitYou(target);
  io.emit('kill', { k: shooter.id, v: target.id, kn: shooter.name, vn: target.name, kf: shooter.faction, vf: target.faction, r: RESPAWN_MS });
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
  io.emit('kill', { k: 0, v: p.id, kn: '', vn: p.name, kf: 'ffa', vf: p.faction, r: RESPAWN_MS, why });
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
    if (m.blocks.some(k => groundBlock(k) && Math.abs(v.x - k.x) < k.hx + VEH.hx && Math.abs(v.z - k.z) < k.hz + VEH.hz)) bad.push('vehicle#' + i + ' is inside a block');
    if (surfaceY(m, v.x, v.z, .1) < -.05) bad.push('vehicle#' + i + ' is not on a floor');
  });
  return bad;
}

// ---- matches and maps ----
const nextMapId = () => MAP_ENV !== 'rotate' ? MAP_ENV : MAP_IDS[(MAP_IDS.indexOf(map.id) + 1) % MAP_IDS.length];

function endMatch(winner, wf, winners) {
  if (match.state !== 'live') return;
  match.state = 'over';
  for (const p of winners || []) grant(p, 0, WIN_CREDITS, 'win');
  const next = MODE === 'rotate' ? (match.mode === 'tdm' ? 'ffa' : 'tdm') : match.mode, nextMap = nextMapId();
  io.emit('match', { ...matchInfo(), winner, wf, next, nextMap: MAPS[nextMap].name, ms: INTERMISSION_MS });
  nextTimer = setTimeout(() => startMatch(next, nextMap), INTERMISSION_MS);
}

function startMatch(mode, mapId) {
  clearTimeout(nextTimer);
  map = MAPS[mapId] || map;
  match.mode = mode; match.state = 'live'; match.team = { vanguard: 0, horizon: 0 };
  vehicles = map.vehicles.map((d, i) => ({ id: i + 1, x: d.x, z: d.z, yaw: d.yaw, speed: 0, driver: null, dirty: false }));
  for (const p of players.values()) p.vehicle = 0;
  const list = [...players.values()].sort(() => Math.random() - .5), flip = Math.random() < .5 ? 1 : 0;   // random split into teams
  list.forEach((p, i) => { p.kills = p.deaths = 0; p.faction = mode === 'tdm' ? ((i + flip) % 2 ? 'horizon' : 'vanguard') : 'ffa'; });
  io.emit('map', clientMap(map));
  io.emit('vehicles', vehRows());
  io.emit('match', matchInfo());
  io.emit('factions', list.map(p => [p.id, p.faction]));
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
  if (q.map !== undefined || q.mode !== undefined) startMatch(q.mode || match.mode, q.map || map.id);
  res.json({ ok: true, map: map.id, mode: match.mode, maps: MAP_IDS });
});

// ---- connections ----
io.on('connection', socket => {
  if (players.size >= MAX_PLAYERS) { socket.emit('full'); socket.disconnect(true); return; }
  const id = nextId++;
  const auth = (socket.handshake && socket.handshake.auth) || {};
  const token = typeof auth.token === 'string' && /^[a-f0-9]{32}$/.test(auth.token) ? auth.token : crypto.randomBytes(16).toString('hex');
  let prof = store.get(token);
  if (!prof) { prof = adopt(token, auth.save); if (prof) store.set(token, prof); else prof = newProfile(); }   // from the browser's signed backup, or brand new
  const me = {
    id, sock: socket, token, prof, shopAt: 0, name: 'Pilot ' + id, faction: pickFaction(), x: 0, y: 0, z: 0, yaw: 0, pitch: 0, last: 0, lastVeh: 0, useAt: 0,
    hp: HP, alive: true, kills: 0, deaths: 0, ammos: WEAPONS.map(w => w.mag), wi: 0, vehicle: 0, reloadEnd: 0, nextShot: 0, respawnAt: 0, epoch: 0, rtt: 100, hist: [], nameAt: 0
  };
  const sp = pickSpawn(me); Object.assign(me, { x: sp.x, y: sp.y, z: sp.z, yaw: sp.yaw });   // a safe point from the spawn matrix
  players.set(socket.id, me);
  socket.emit('welcome', {
    ...pub(me), hp: me.hp, ammos: me.ammos, wi: me.wi, weapons: WEAPONS, map: clientMap(map), vehicles: vehRows(), token, profile: profileView(me), skins: SKINS,
    match: matchInfo(), players: [...players.values()].filter(p => p !== me).map(pub)
  });
  socket.broadcast.emit('join', pub(me));
  console.log(`+ ${me.name} (${me.faction}), ${players.size} online, ${match.mode} on ${map.id}`);

  socket.on('state', d => {
    const now = Date.now();
    if (!d || !me.alive || me.vehicle || d.e !== me.epoch || now - me.last < 15) return;     // dead, driving, stale (before a respawn) or flooding
    if (![d.x, d.y, d.z, d.yaw, d.pitch].every(n => typeof n === 'number' && Number.isFinite(n))) return;
    me.last = now;
    const b = map.bounds, pad = b.edge === 'void' ? 12 : 0;   // wall maps stop you at the box; a void map lets you step past it, and that is a death
    me.x = r2(clamp(d.x, b.min[0] - pad, b.max[0] + pad)); me.y = r2(clamp(d.y, b.min[1] - 12, b.max[1])); me.z = r2(clamp(d.z, b.min[2] - pad, b.max[2] + pad));
    me.yaw = r3(clamp(d.yaw, -Math.PI, Math.PI)); me.pitch = r3(clamp(d.pitch, -Math.PI / 2, Math.PI / 2));
  });

  socket.on('shoot', d => {
    const now = Date.now(), w = W(me);
    if (!d || !me.alive || me.vehicle || match.state !== 'live' || me.reloadEnd || now < me.nextShot) return;   // fire rate, reload and driving are enforced here
    if (!['ox', 'oy', 'oz', 'dx', 'dy', 'dz'].every(k => typeof d[k] === 'number' && Number.isFinite(d[k]))) return;
    const len = Math.hypot(d.dx, d.dy, d.dz);
    if (len < .5) return;
    const o = { x: d.ox, y: d.oy, z: d.oz }, dir = { x: d.dx / len, y: d.dy / len, z: d.dz / len };
    if (Math.hypot(o.x - me.x, o.y - (me.y + BODY.eye), o.z - me.z) > 6) return;   // the ray must start near the shooter
    if (me.ammos[me.wi] <= 0) { startReload(me); return; }
    me.nextShot = now + (1000 / w.fireRate) * .8; me.ammos[me.wi]--;
    const hit = cast(me, o, dir, w.range), t = hit.t;
    socket.broadcast.emit('fx', {                                                    // let everyone else see the tracer
      a: [r2(me.x + dir.x * .7), r2(me.y + BODY.eye + dir.y * .7), r2(me.z + dir.z * .7)],
      b: [r2(o.x + dir.x * t), r2(o.y + dir.y * t), r2(o.z + dir.z * t)], f: me.faction, s: profOf(me).eq.weapon
    });
    if (hit.who) hurt(me, hit.who, w.damage);
    if (me.alive && me.ammos[me.wi] <= 0) startReload(me);
  });

  socket.on('reload', () => { if (me.alive && !me.vehicle && match.state === 'live') startReload(me); });

  socket.on('switch', i => {                      // changing weapon cancels a reload and costs a short draw time
    if (!Number.isInteger(i) || i < 0 || i >= WEAPONS.length || i === me.wi || !me.alive || me.vehicle) return;
    me.wi = i; me.reloadEnd = 0; me.nextShot = Math.max(me.nextShot, Date.now() + SWITCH_MS);
    emitYou(me);
  });

  socket.on('use', () => {                        // the E key
    const now = Date.now();
    if (!me.alive || match.state !== 'live' || now - me.useAt < 250) return;
    me.useAt = now;
    if (me.vehicle) { leaveVehicle(me, true); return; }
    let best = null, bd = VEH.useRange;
    for (const v of vehicles) { if (v.driver) continue; const d = distToVehicle(v, me.x, me.z); if (d <= bd) { best = v; bd = d; } }
    if (!best) return;
    best.driver = me; me.vehicle = best.id; me.reloadEnd = 0;
    socket.emit('drive', { vid: best.id, x: best.x, z: best.z, yaw: best.yaw });
    io.emit('vehicles', vehRows());
  });

  socket.on('veh', d => {                         // the driver reports the vehicle's pose
    const v = me.vehicle && vehicles.find(x => x.id === me.vehicle), now = Date.now();
    if (!v || !d || !me.alive || now - me.lastVeh < 15) return;
    if (![d.x, d.z, d.yaw, d.speed].every(n => typeof n === 'number' && Number.isFinite(n))) return;
    me.lastVeh = now;
    const lim = map.half - VEH.hx;
    v.x = r2(clamp(d.x, -lim, lim)); v.z = r2(clamp(d.z, -lim, lim)); v.yaw = r3(wrap(d.yaw)); v.speed = r2(clamp(d.speed, -VEH.maxReverse, VEH.maxSpeed));
    me.x = v.x; me.z = v.z; me.y = 0; v.dirty = true;
  });

  socket.on('buy', id => {                        // spend credits on a skin; buying also equips it
    const s = skinById.get(id), pr = profOf(me), now = Date.now();
    if (!s || now - me.shopAt < 200) return; me.shopAt = now;
    if (pr.owned.includes(id)) return notice(me, 'You already own that');
    if (levelInfo(pr.xp).level < s.level) return notice(me, 'Reach level ' + s.level + ' to unlock this');
    if (pr.credits < s.price) return notice(me, 'Not enough credits');
    pr.credits -= s.price; pr.owned.push(id);
    equip(me, s);
  });

  socket.on('equip', id => {
    const s = skinById.get(id), now = Date.now();
    if (!s || now - me.shopAt < 200) return; me.shopAt = now;
    if (!profOf(me).owned.includes(id)) return notice(me, 'Unlock that skin first');
    equip(me, s);
  });

  socket.on('name', n => {
    const now = Date.now(), nm = cleanName(n, me.id);
    if (now - me.nameAt < 1000 || nm === me.name) return;
    me.nameAt = now; me.name = nm;
    io.emit('rename', { id: me.id, name: nm });
  });

  socket.on('disconnect', () => {
    if (me.vehicle) leaveVehicle(me, false);
    players.delete(socket.id);
    io.emit('leave', me.id);
    console.log(`- ${me.name}, ${players.size} online`);
  });
});

// The heartbeat: 20 times a second. Records history for lag compensation, finishes reloads, respawns the dead,
// measures each player's round-trip time, and sends everybody one snapshot (plus vehicle poses when one moved).
setInterval(() => {
  const now = Date.now(); tick++;
  for (const p of players.values()) {
    if (p.alive) { p.hist.push({ t: now, x: p.x, y: p.y, z: p.z }); if (p.hist.length > 25) p.hist.shift(); }
    else if (match.state === 'live' && now >= p.respawnAt) respawn(p);
    if (p.alive && !p.vehicle && match.state === 'live') { const why = oobReason(p); if (why) eliminate(p, why); }   // out of bounds or in a kill zone
    if (p.reloadEnd && now >= p.reloadEnd) { p.reloadEnd = 0; p.ammos[p.wi] = W(p).mag; emitYou(p); }
    if (tick % (TICK_HZ * 2) === 0) { const t0 = now; p.sock.emit('lag', () => { p.rtt = Math.min(1000, Date.now() - t0); }); }
  }
  if (!players.size) return;
  const list = [...players.values()].map(p => [p.id, p.x, p.y, p.z, p.yaw, p.pitch, p.alive ? 1 : 0, p.vehicle, p.wi]);
  const moved = vehicles.some(v => v.dirty), rows = moved ? vehRows() : null;
  vehicles.forEach(v => { v.dirty = false; });
  for (const s of io.sockets.sockets.values()) { s.volatile.emit('snapshot', list); if (moved) s.volatile.emit('vehicles', rows); }
}, 1000 / TICK_HZ);

for (const m of Object.values(MAPS)) { const bad = validateMap(m); if (bad.length) console.error('MAP PROBLEM in ' + m.id + ':\n  ' + bad.join('\n  ')); }
startMatch(MODE === 'rotate' ? 'tdm' : MODE, MAP_ENV === 'rotate' ? 'field' : MAP_ENV);
for (const sig of ['SIGTERM', 'SIGINT']) process.on(sig, () => { store.flush(); process.exit(0); });   // save on a clean shutdown
server.listen(PORT, () => console.log(`Riftline server listening on port ${PORT}, mode ${MODE}, map ${MAP_ENV}`));

if (require.main !== module) module.exports = { MAPS, validateMap, surfaceY, rayRamp, rayBox, rampY, clientMap };   // lets the tests reach the geometry helpers
