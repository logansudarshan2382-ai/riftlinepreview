'use strict';
/*
 * Riftline game server (Step 5): modes, three weapons, two maps, and a drivable vehicle.
 *
 * Environment variables (all optional):
 *   MODE       tdm | ffa            lock one game mode (default: alternate every match)
 *   MAP        field | arena        lock one map (default: alternate every match)
 *   ADMIN_KEY  any secret text      turns on /admin so you can load a map or mode on the spot (see below)
 *   TDM_LIMIT, FFA_LIMIT            kills needed to win
 *   ALLOWED_ORIGINS                 your website address(es), comma separated
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
 *                    you {hp,ammos,wi,reloading}  hit  fx  kill  scores  respawn
 *
 * The server decides every hit, kill and point, and owns the weapon and map tables (clients just follow them).
 * Player and vehicle positions are still reported by the client and only sanity-checked.
 */
const express = require('express');
const http = require('http');
const path = require('path');
const crypto = require('crypto');
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

// ---- weapons: the first one is what everybody spawns with. Add a line here and it appears in the game. ----
const WEAPONS = [
  { name: 'Rift pistol',   short: 'PISTOL', damage: 20, fireRate: 6,   mag: 12, reload: 1.5, range: 150, auto: false },
  { name: 'Assault rifle', short: 'RIFLE',  damage: 12, fireRate: 11,  mag: 30, reload: 2.0, range: 120, auto: true },
  { name: 'Sniper rifle',  short: 'SNIPER', damage: 75, fireRate: .9,  mag: 5,  reload: 2.6, range: 300, auto: false }
];

// ---- maps: blocks are solid boxes (centre x/z, half-sizes hx/hz, height h). Add a map here and /admin can load it. ----
const B = (x, z, hx, hz, h) => ({ x, z, hx, hz, h });
const MAPS = {
  field: {   // open ground with tall pillars and low cover
    id: 'field', name: 'Pillar Fields', half: 60, sky: 0x0f1530, fog: [40, 140], sun: true, ceiling: 0, lights: [], tint: 0x3a4780,
    blocks: [B(-14, -14, 1, 1, 7), B(14, -14, 1, 1, 7), B(-14, 14, 1, 1, 7), B(14, 14, 1, 1, 7),
             B(-32, -8, 1, 1, 7), B(32, -8, 1, 1, 7), B(-32, 8, 1, 1, 7), B(32, 8, 1, 1, 7),
             B(0, -6, 2, .6, 1), B(-8, 4, .6, 2, 1), B(8, 4, .6, 2, 1), B(0, 22, 3, .6, 1.2)],
    spawns: [[-44, -44], [44, -44], [-44, 44], [44, 44], [0, -46], [0, 46], [-46, 0], [46, 0]],
    vehicles: [{ x: 0, z: 12, yaw: 0 }]
  },
  arena: {   // a small indoor arena: walls, doorways, a central block and a ceiling
    id: 'arena', name: 'Close Quarters', half: 24, sky: 0x07090f, fog: [10, 55], sun: false, ceiling: 6, lights: [[0, 5, -14], [0, 5, 14]], tint: 0x4a5272,
    blocks: [B(0, -24.5, 25, .5, 5), B(0, 24.5, 25, .5, 5), B(-24.5, 0, .5, 25, 5), B(24.5, 0, .5, 25, 5),
             B(-12, -10, 6, .5, 4), B(12, -10, 6, .5, 4), B(-12, 10, 6, .5, 4), B(12, 10, 6, .5, 4),
             B(0, 0, 2, 2, 3), B(-16, 0, .5, 3, 2.5), B(16, 0, .5, 3, 2.5),
             B(-6, -18, 1, 1, 1), B(6, -18, 1, 1, 1), B(-6, 18, 1, 1, 1), B(6, 18, 1, 1, 1)],
    spawns: [[-20, -20], [20, -20], [-20, 20], [20, 20], [0, -20], [0, 20], [-20, 0], [20, 0]],
    vehicles: [{ x: 0, z: 16, yaw: 0 }]
  }
};
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
const pub = p => ({ id: p.id, name: p.name, faction: p.faction, kills: p.kills, deaths: p.deaths, alive: p.alive, x: p.x, y: p.y, z: p.z, yaw: p.yaw, pitch: p.pitch });
const matchInfo = () => ({ mode: match.mode, limit: LIMIT[match.mode], state: match.state, team: match.team, map: map.name });
const sendScores = () => io.emit('scores', { t: match.team, p: [...players.values()].map(p => [p.id, p.kills, p.deaths]) });
const vehRows = () => vehicles.map(v => [v.id, r2(v.x), r2(v.z), r3(v.yaw), v.driver ? v.driver.id : 0]);
const emitYou = p => p.sock.emit('you', { hp: p.hp, ammos: p.ammos, wi: p.wi, reloading: !!p.reloadEnd });
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

function respawn(p) {
  const [x, z] = map.spawns[Math.floor(Math.random() * map.spawns.length)];
  Object.assign(p, { x, y: 0, z, hp: HP, alive: true, ammos: WEAPONS.map(w => w.mag), reloadEnd: 0, nextShot: 0, vehicle: 0, epoch: p.epoch + 1, hist: [] });
  p.sock.emit('respawn', { x, z, hp: HP, ammos: p.ammos, wi: p.wi, e: p.epoch });   // e: old position updates still in flight are ignored
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
// The vehicle box is turned by its yaw, so rotate the ray into the vehicle's own frame first.
function rayVehicle(o, d, v) {
  const c = Math.cos(v.yaw), s = Math.sin(v.yaw), dx = o.x - v.x, dz = o.z - v.z;
  return rayBox({ x: dx * c - dz * s, y: o.y, z: dx * s + dz * c }, { x: d.x * c - d.z * s, y: d.y, z: d.x * s + d.z * c }, -VEH.hx, 0, -VEH.hz, VEH.hx, VEH.h, VEH.hz);
}
function distToVehicle(v, x, z) {   // ground-plane distance from a point to the vehicle's body (0 = touching)
  const c = Math.cos(v.yaw), s = Math.sin(v.yaw), dx = x - v.x, dz = z - v.z;
  return Math.hypot(Math.max(Math.abs(dx * c - dz * s) - VEH.hx, 0), Math.max(Math.abs(dx * s + dz * c) - VEH.hz, 0));
}
function exitSpot(v) {   // first free spot beside the vehicle: right, left, behind, in front
  const c = Math.cos(v.yaw), s = Math.sin(v.yaw), lim = map.half - BODY.r;
  for (const [lx, lz] of [[VEH.hx + 1, 0], [-VEH.hx - 1, 0], [0, VEH.hz + 1], [0, -VEH.hz - 1]]) {
    const x = v.x + lx * c + lz * s, z = v.z - lx * s + lz * c;
    if (Math.abs(x) <= lim && Math.abs(z) <= lim && !map.blocks.some(b => Math.abs(x - b.x) < b.hx + BODY.r && Math.abs(z - b.z) < b.hz + BODY.r)) return { x, z };
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
  if (d.y < -1e-6) { const t = -o.y / d.y; if (t > 0 && t < best.t) best = { t, who: null }; }
  for (const b of map.blocks) {
    const t = rayBox(o, d, b.x - b.hx, 0, b.z - b.hz, b.x + b.hx, b.h, b.z + b.hz);
    if (t !== null && t < best.t) best = { t, who: null };
  }
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
  emitYou(target);
  io.emit('kill', { k: shooter.id, v: target.id, kn: shooter.name, vn: target.name, kf: shooter.faction, vf: target.faction, r: RESPAWN_MS });
  sendScores();
  if (match.mode === 'tdm' && match.team[shooter.faction] >= LIMIT.tdm) endMatch(shooter.faction.toUpperCase() + ' WINS', shooter.faction);
  else if (match.mode === 'ffa' && shooter.kills >= LIMIT.ffa) endMatch(shooter.name + ' WINS', 'ffa');
}

// ---- matches and maps ----
const nextMapId = () => MAP_ENV !== 'rotate' ? MAP_ENV : MAP_IDS[(MAP_IDS.indexOf(map.id) + 1) % MAP_IDS.length];

function endMatch(winner, wf) {
  if (match.state !== 'live') return;
  match.state = 'over';
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
  io.emit('map', map);
  io.emit('vehicles', vehRows());
  io.emit('match', matchInfo());
  io.emit('factions', list.map(p => [p.id, p.faction]));
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
  const id = nextId++, [sx, sz] = map.spawns[spawnIx++ % map.spawns.length];
  const me = {
    id, sock: socket, name: 'Pilot ' + id, faction: pickFaction(), x: sx, y: 0, z: sz, yaw: 0, pitch: 0, last: 0, lastVeh: 0, useAt: 0,
    hp: HP, alive: true, kills: 0, deaths: 0, ammos: WEAPONS.map(w => w.mag), wi: 0, vehicle: 0, reloadEnd: 0, nextShot: 0, respawnAt: 0, epoch: 0, rtt: 100, hist: [], nameAt: 0
  };
  players.set(socket.id, me);
  socket.emit('welcome', {
    ...pub(me), hp: me.hp, ammos: me.ammos, wi: me.wi, weapons: WEAPONS, map, vehicles: vehRows(),
    match: matchInfo(), players: [...players.values()].filter(p => p !== me).map(pub)
  });
  socket.broadcast.emit('join', pub(me));
  console.log(`+ ${me.name} (${me.faction}), ${players.size} online, ${match.mode} on ${map.id}`);

  socket.on('state', d => {
    const now = Date.now();
    if (!d || !me.alive || me.vehicle || d.e !== me.epoch || now - me.last < 15) return;     // dead, driving, stale (before a respawn) or flooding
    if (![d.x, d.y, d.z, d.yaw, d.pitch].every(n => typeof n === 'number' && Number.isFinite(n))) return;
    me.last = now;
    me.x = r2(clamp(d.x, -map.half, map.half)); me.y = r2(clamp(d.y, 0, 30)); me.z = r2(clamp(d.z, -map.half, map.half));
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
      b: [r2(o.x + dir.x * t), r2(o.y + dir.y * t), r2(o.z + dir.z * t)], f: me.faction
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
    if (p.reloadEnd && now >= p.reloadEnd) { p.reloadEnd = 0; p.ammos[p.wi] = W(p).mag; emitYou(p); }
    if (tick % (TICK_HZ * 2) === 0) { const t0 = now; p.sock.emit('lag', () => { p.rtt = Math.min(1000, Date.now() - t0); }); }
  }
  if (!players.size) return;
  const list = [...players.values()].map(p => [p.id, p.x, p.y, p.z, p.yaw, p.pitch, p.alive ? 1 : 0, p.vehicle]);
  const moved = vehicles.some(v => v.dirty), rows = moved ? vehRows() : null;
  vehicles.forEach(v => { v.dirty = false; });
  for (const s of io.sockets.sockets.values()) { s.volatile.emit('snapshot', list); if (moved) s.volatile.emit('vehicles', rows); }
}, 1000 / TICK_HZ);

startMatch(MODE === 'rotate' ? 'tdm' : MODE, MAP_ENV === 'rotate' ? 'field' : MAP_ENV);
server.listen(PORT, () => console.log(`Riftline server listening on port ${PORT}, mode ${MODE}, map ${MAP_ENV}`));
