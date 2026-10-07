'use strict';
/*
 * Riftline game server (Step 3): relays player poses between everyone in one shared arena.
 *
 *   client -> server   'state'    { x, y, z, yaw, pitch }   about 20x/s (the player's own pose)
 *   client -> server   'faction'  'vanguard' | 'horizon' | 'ffa'
 *   server -> client   'welcome'  { id, faction, x, y, z, players: [...] }   sent once, to the new player only
 *   server -> others   'join'     { id, faction, x, y, z, yaw, pitch }       "spawn a capsule for this player"
 *   server -> everyone 'snapshot' [[id, x, y, z, yaw, pitch], ...]           20x/s, every player in one message
 *   server -> everyone 'faction'  { id, faction }  and  'leave' id
 *
 * Positions are reported by each client and only sanity-checked here. Moving the movement
 * simulation onto the server (so it can't be faked) is the next upgrade.
 */
const express = require('express');
const http = require('http');
const path = require('path');
const { Server } = require('socket.io');

const PORT = process.env.PORT || 3000;
// The arcade site lives on a different host than this server, so list its address(es) here.
// Any http://localhost:<port> is always allowed for local testing.
const ORIGINS = (process.env.ALLOWED_ORIGINS || 'https://fungames-arcade.netlify.app').split(',').map(s => s.trim());
const TICK_HZ = 20, MAX_PLAYERS = 16, ARENA_HALF = 60;
const FACTIONS = ['vanguard', 'horizon', 'ffa'];
const SPAWNS = [[4, 4], [-4, 4], [4, -4], [-4, -4], [0, 8], [8, 2], [-8, 2], [0, -6]];   // clear of the blocks in the arena

const players = new Map();   // socket.id -> { id, faction, x, y, z, yaw, pitch, last }
let nextId = 1, spawnIx = 0;

const app = express();
if (process.env.SITE_DIR) app.use(express.static(path.resolve(process.env.SITE_DIR)));   // optional: serve the arcade locally too
app.get('/health', (req, res) => res.json({ ok: true, players: players.size }));

const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: (origin, cb) => cb(null, !origin || ORIGINS.includes(origin) || /^http:\/\/(localhost|127\.0\.0\.1)(:\d+)?$/.test(origin)) },
  maxHttpBufferSize: 1e4   // our messages are tiny; refuse big ones
});

const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));
const r2 = v => Math.round(v * 100) / 100, r3 = v => Math.round(v * 1000) / 1000;
const pub = p => ({ id: p.id, faction: p.faction, x: p.x, y: p.y, z: p.z, yaw: p.yaw, pitch: p.pitch });

io.on('connection', socket => {
  if (players.size >= MAX_PLAYERS) { socket.emit('full'); socket.disconnect(true); return; }

  // Keep the two factions balanced: the new player joins whichever side has fewer players.
  const count = { vanguard: 0, horizon: 0 };
  for (const p of players.values()) if (p.faction in count) count[p.faction]++;
  const [sx, sz] = SPAWNS[spawnIx++ % SPAWNS.length];
  const me = { id: nextId++, faction: count.horizon < count.vanguard ? 'horizon' : 'vanguard', x: sx, y: 0, z: sz, yaw: 0, pitch: 0, last: 0 };
  players.set(socket.id, me);

  socket.emit('welcome', { ...pub(me), players: [...players.values()].filter(p => p !== me).map(pub) });
  socket.broadcast.emit('join', pub(me));
  console.log(`+ player ${me.id} (${me.faction}), ${players.size} online`);

  socket.on('state', d => {
    const now = Date.now();
    if (!d || now - me.last < 15) return;                       // ignore floods; clients send every ~50 ms
    const v = [d.x, d.y, d.z, d.yaw, d.pitch];
    if (!v.every(n => typeof n === 'number' && Number.isFinite(n))) return;   // reject NaN, Infinity and wrong types
    me.last = now;
    me.x = r2(clamp(d.x, -ARENA_HALF, ARENA_HALF)); me.y = r2(clamp(d.y, 0, 30)); me.z = r2(clamp(d.z, -ARENA_HALF, ARENA_HALF));
    me.yaw = r3(clamp(d.yaw, -Math.PI, Math.PI)); me.pitch = r3(clamp(d.pitch, -Math.PI / 2, Math.PI / 2));
  });

  socket.on('faction', f => {
    if (!FACTIONS.includes(f)) return;
    me.faction = f;
    io.emit('faction', { id: me.id, faction: f });
  });

  socket.on('disconnect', () => {
    players.delete(socket.id);
    io.emit('leave', me.id);
    console.log(`- player ${me.id}, ${players.size} online`);
  });
});

// One snapshot of everybody, 20 times a second. "Volatile": if a client is lagging, skip the stale one instead of queueing it.
setInterval(() => {
  if (!players.size) return;
  const list = [...players.values()].map(p => [p.id, p.x, p.y, p.z, p.yaw, p.pitch]);
  for (const s of io.sockets.sockets.values()) s.volatile.emit('snapshot', list);
}, 1000 / TICK_HZ);

server.listen(PORT, () => console.log(`Riftline server listening on port ${PORT}`));
