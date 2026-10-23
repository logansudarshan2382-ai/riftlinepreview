'use strict';
/*
 * Riftline game server: modes, weapons, five 600 x 600 m natural maps (each with two team bases), vehicles, player progression,
 * a spawn-point matrix and out-of-bounds / kill-zone deaths.
 *
 * Environment variables (all optional):
 *   MODE       tdm | ffa            lock one game mode (default: alternate every match)
 *   MAP        field | glacier | arena | station | frontier   lock one map (default: every match picks a random map, never the same one twice in a row)
 *   ADMIN_KEY  any secret text      turns on /admin so you can load a map or mode on the spot (see below)
 *   TDM_LIMIT, FFA_LIMIT            kills needed to win
 *   ALLOWED_ORIGINS                 your website address(es), comma separated
 *   SAVE_SECRET  any long secret    signs each player's backup save (on Render it defaults to a key derived from the service id, so progress survives restarts). Set your own to keep it private: Render's free plan wipes files on every restart,
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
 *                    award {name}   a multi-kill or a kill streak you just earned (DOUBLE KILL, GODLIKE ...)
 *                    report {win,kills,heads,killXp,headXp,xp,coins,winCoins,levelCoins,from,to,up}   the match is over: what it paid you, for the results card
 * client -> server   getprofile id   ->   pubprofile {name,level,into,need,kills,st,eq,faction}   anyone in the room can open anyone's profile, bots included
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
const LIMIT = { tdm: Number(process.env.TDM_LIMIT) || 40, ffa: Number(process.env.FFA_LIMIT) || 50 };   // kills needed to win: a team deathmatch ends at 40 team kills, a free for all when one player reaches 50. Otherwise the 10 minute clock decides: most team kills, or the top killer
const MATCH_MS = (Number(process.env.MATCH_MINUTES) || 10) * 60000;   // every match lasts 10 minutes at most
const BODY = { r: .4, h: 1.8, eye: 1.62 };
const VEH = { hx: 1.3, hz: 2.5, h: 1.6, maxSpeed: 22, maxReverse: 6, useRange: 1.8, gunRange: 3.6 };
const VTYPES = {   // vehicle classes: footprint, height and speed limits (m/s). A ground car is fast and runs people over; the helicopter flies; the mech walks.
  car:  { hx: 1.3, hz: 2.5, h: 1.6, maxSpeed: 22, maxReverse: 6 },
  heli: { hx: 1.5, hz: 3.4, h: 2.6, maxSpeed: 20, maxReverse: 20 },
  mech: { hx: 1.5, hz: 1.5, h: 5.6, maxSpeed: 4.5, maxReverse: 4.5 },
  tank: { hx: 1.7, hz: 3.0, h: 2.2, maxSpeed: 9, maxReverse: 4 },   // slow, heavy, crushes people it drives over, and fires a shell
  turret: { hx: 1.4, hz: 1.4, h: 1, maxSpeed: 0, maxReverse: 0 }    // a manned gun nest on top of a pillar: it never moves, the footprint is where you climb out
};
const vd = v => VTYPES[v.type] || VTYPES.car;
// Vehicle armour. Shots that hit a vehicle now wear down the vehicle, not the person inside, until it blows up. `hp` is its hit points; light / mid / heavy is the share of a shot's damage that gets through,
// by the weight of the weapon: light = rifles, SMGs, pistols, shotgun pellets, minigun; mid = sniper rifles, magnums, marksman rifles (26+ damage a shot); heavy = launchers, grenades, anti-materiel and rail rifles, vehicle cannons.
// The mech is well armoured but has a weak spot: its glowing reactor on the upper back takes triple damage and ignores its armour. Gun nests on pillars and base sentry seats are not vehicles in this sense and cannot be destroyed.
const VARM = { car: { hp: 450, light: .8, mid: .88, heavy: 1 }, tank: { hp: 1700, light: .5, mid: .64, heavy: .85 }, heli: { hp: 550, light: .8, mid: .88, heavy: 1 }, mech: { hp: 1200, light: .6, mid: .64, heavy: .7, weak: 3 } };   // car = Protector Jeep, heli = Guardian, mech = Overseer, tank = Hammerhead. `light` is the share of small-arms damage that gets through (0.8 = takes 20% less), mid sits between light and heavy
const VEH_RESPAWN_MS = 60000;   // a wreck stays as cover for a minute, then the vehicle is back where it started
const weightOf = w => (w.splash && w.splash.damage >= 40) || w.damage >= 70 || (w.pierce || 0) >= 2 ? 'heavy' : w.damage >= 26 ? 'mid' : 'light';
const VWEAPONS = {   // what a driver's left click fires. Helicopter rockets are slow; the mech's miniguns heat up (+2.2 a shot, cooling 18 a second, locked for 2.5 s at 100)
  heli: { damage: 100, headshotMultiplier: 1, fireRateDelay: 1400, range: 300, splash: { radius: 8, damage: 90 } },
  mech: { damage: 5, headshotMultiplier: 1, fireRateDelay: 45, range: 120, heat: 2.2 },
  tank: { damage: 100, headshotMultiplier: 1, fireRateDelay: 1600, range: 300, splash: { radius: 7, damage: 90 } },
  turret: { damage: 14, headshotMultiplier: 1.5, fireRateDelay: 90, range: 150 },   // a pillar-top gun
  cargun: { damage: 9, headshotMultiplier: 1.3, fireRateDelay: 75, range: 110 }      // the roof gun of a car, fired by a passenger
};
const TURRET = { radius: 120, damage: 6, headshotMultiplier: 1, fireRateDelay: 110, range: 125, top: 14, head: 1.6, reach: 1.7 };   // base sentries: they stand on a 14 m tower (as high as the sniper decks) and scan 120 m around it; `head` is how far above the tower top the gun sits and `reach` how far its muzzle sticks out sideways

// ---- progression: XP, levels, coins and skins, saved per player ----
const XP_PER_KILL = 100, XP_PER_HEADSHOT = 100, COINS_PER_KILL = 10, WIN_COINS = 50, LEVEL_UP_COINS = 25, MAX_PROFILES = 5000;
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
// Profile stats (the Profile screen). Kills live on the profile itself; everything else is counted here and saved with it.
// deaths, games (matches played to the end), wins, winStreak (matches won in a row, right now) and its best, vehKills (vehicles destroyed), headshots, doubleKills / tripleKills (kills in quick succession),
// sprees / dominating / unstoppable / godlike (kill streaks without dying: 3, 5, 7 and 10), bestStreak (longest kill streak)
const STAT_KEYS = ['deaths', 'games', 'wins', 'winStreak', 'bestWinStreak', 'vehKills', 'headshots', 'doubleKills', 'tripleKills', 'sprees', 'dominating', 'unstoppable', 'godlike', 'bestStreak'];
const STREAKS = { 3: ['sprees', 'KILLING SPREE'], 5: ['dominating', 'DOMINATING'], 7: ['unstoppable', 'UNSTOPPABLE'], 10: ['godlike', 'GODLIKE'] }, MULTI_MS = 4000;   // a kill within 4 s of the last one chains: 2 = double, 3 = triple
const statNum = v => Math.max(0, Math.floor(Number(v)) || 0);
const statsClean = s => { const o = {}; for (const k of STAT_KEYS) { const v = statNum(s && s[k]); if (v) o[k] = v; } return o; };   // only the non-zero ones, as whole numbers: what is saved and signed
const statsFull = s => { const o = {}; for (const k of STAT_KEYS) o[k] = statNum(s && s[k]); return o; };                           // every stat, zeros included: what the client shows
const newProfile = () => ({ xp: 0, coins: 0, kills: 0, owned: ['issue', 'w-issue', 'f-raider'], eq: { body: 'issue', weapon: 'w-issue', frame: 'f-raider', loadout: [0, 1, 3] }, st: {}, rev: 0, seen: Date.now() });

// The "mock database": every profile in one JSON file, keyed by a secret token that the player's browser keeps.
// Render's free plan wipes local files on every restart or sleep, so each player's browser also holds a signed backup
// (see sign/adopt below). The signature uses SAVE_SECRET, so a player can't edit their own XP or coins.
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
// The secret that signs every player's backup save. A save only restores if it was signed with the same secret, so the secret must not change when the server restarts.
// SAVE_SECRET wins if it is set. Otherwise, on Render, one is derived from the service's own id (it is the same after every restart and redeploy, and is not in this file for anyone to read).
const stableSecret = () => process.env.RENDER_SERVICE_ID ? crypto.createHash('sha256').update('riftline-save-key:' + process.env.RENDER_SERVICE_ID).digest('hex') : null;
const SAVE_SECRET = process.env.SAVE_SECRET || stableSecret() || crypto.randomBytes(32).toString('hex');
if (!process.env.SAVE_SECRET) console.warn(process.env.RENDER_SERVICE_ID ? "SAVE_SECRET is not set: signing backup saves with a key derived from this Render service's id, so progress survives restarts. Set SAVE_SECRET to choose your own." : "SAVE_SECRET is not set and this is not Render: players' backup saves will stop working whenever this server restarts.");
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
  const body = Buffer.from(JSON.stringify({ t: token, xp: p.xp, coins: p.coins, kills: p.kills, owned: p.owned, eq: p.eq, st: statsClean(p.st) })).toString('base64url');
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
    return { xp: n(d.xp), coins: n(d.coins != null ? d.coins : d.credits), kills: n(d.kills), owned, eq: { body: worn(d.eq && d.eq.body, 'body', 'issue'), weapon: worn(d.eq && d.eq.weapon, 'weapon', 'w-issue'), frame: worn(d.eq && d.eq.frame, 'frame', 'f-raider'), loadout: cleanLoadout(d.eq && d.eq.loadout) }, st: statsClean(d.st), rev: 1, seen: Date.now() };
  } catch (e) { return null; }
}

// ---- weapons: the first one is what everybody spawns with. Add a line here and it appears in the game. ----
const BASE_WEAPONS = [   // damage per bullet, delay between shots (ms), magazine size, spare ammo (maxAmmo), reload seconds, range in metres, level needed. HP is 100.
  // Per player, currentMagazine is p.ammos[i] and currentAmmo (the spare rounds) is p.reserve[i]. `splash` = explosion radius (m) and damage at its centre.
  { name: 'Assault rifle',   short: 'RIFLE',  damage: 7,   headshotMultiplier: 1.5, fireRateDelay: 70,   magazineSize: 250, maxAmmo: 750, reloadTime: 1.4, range: 60,  unlockLevel: 1,  auto: true,  len: 1 },
  { name: 'Sniper rifle',    short: 'SNIPER', damage: 50,  headshotMultiplier: 2,   fireRateDelay: 450,  magazineSize: 5,   maxAmmo: 20,  reloadTime: 4.5, range: 400, unlockLevel: 5,  auto: false, len: 1.5 },
  { name: 'Rocket launcher', short: 'ROCKET', damage: 85, headshotMultiplier: 1,   fireRateDelay: 1800, magazineSize: 1,   maxAmmo: 6,   reloadTime: 5,   range: 250, unlockLevel: 10, auto: false, len: 1.4, splash: { radius: 7, damage: 70 } }
];

// ---- the armoury: the three originals above plus 50 more. Extra properties: pellets (rays per shot), spread (inaccuracy), falloff [full-damage range, zero range, minimum multiplier], pierce (extra targets a shot passes through),
//      splash {radius, damage}, burn {dps, secs}, lifesteal (share of damage healed), zoom (scope field of view), moveMult (walking speed while held), ammoPerShot. Players carry three (keys 1-3), picked in the shop's Loadout tab.
const LEN = { Pistol: .6, SMG: .75, Rifle: 1, Shotgun: 1, LMG: 1.2, Marksman: 1.5, Launcher: 1.4, Energy: 1 };
const ROWS = [   // name, short, class, unlock level, damage, delay ms, magazine, reserve, reload s, range m, extras
  ['Pistol', 'PISTOL', 'Pistol', 1, 14, 220, 15, 90, 1, 45, { headshotMultiplier: 1.8 }],
  ['Machine pistol', 'MPISTOL', 'Pistol', 3, 5, 55, 30, 180, 1.3, 35, { auto: true, spread: .03 }],
  ['Revolver', 'REVOLVER', 'Pistol', 6, 38, 600, 6, 36, 2.2, 55, { headshotMultiplier: 2 }],
  ['Plasma pistol', 'PLASMAP', 'Pistol', 11, 20, 300, 12, 72, 1.5, 50, { splash: { radius: 2, damage: 14 } }],
  ['Hand cannon', 'HCANNON', 'Pistol', 14, 55, 900, 5, 25, 2.5, 60, { headshotMultiplier: 1.7 }],
  ['Gauss pistol', 'GAUSSP', 'Pistol', 25, 45, 700, 8, 40, 2, 70, { pierce: 1 }],
  ['SMG', 'SMG', 'SMG', 2, 6, 60, 32, 192, 1.4, 40, { auto: true, spread: .02 }],
  ['Mini SMG', 'MINI', 'SMG', 4, 4, 40, 40, 240, 1.2, 30, { auto: true, spread: .04, moveMult: 1.1 }],
  ['Vector', 'VECTOR', 'SMG', 8, 5, 45, 25, 150, 1.6, 35, { auto: true, spread: .03 }],
  ['Compact PDW', 'PDW', 'SMG', 12, 7, 75, 30, 150, 1.5, 45, { auto: true, spread: .015 }],
  ['Heavy SMG', 'HSMG', 'SMG', 18, 9, 85, 30, 150, 1.8, 42, { auto: true, spread: .02 }],
  ['Vampire SMG', 'VAMP', 'SMG', 24, 6, 65, 30, 150, 1.6, 38, { auto: true, spread: .02, lifesteal: .25 }],
  ['Carbine', 'CARBINE', 'Rifle', 3, 6, 60, 30, 150, 1.4, 55, { auto: true, spread: .012 }],
  ['Battle rifle', 'BATTLE', 'Rifle', 9, 11, 110, 24, 120, 1.7, 70, { auto: true }],
  ['Burst rifle', 'BURST', 'Rifle', 13, 8, 300, 36, 180, 1.8, 70, { pellets: 3, ammoPerShot: 3, spread: .012 }],
  ['Heavy rifle', 'HEAVYR', 'Rifle', 16, 12, 120, 20, 100, 2, 75, { auto: true, headshotMultiplier: 1.7 }],
  ['Scout rifle', 'SCOUT', 'Rifle', 20, 8, 80, 25, 125, 1.5, 85, { auto: true, zoom: 55 }],
  ['Tactical rifle', 'TACTICAL', 'Rifle', 26, 9, 90, 30, 150, 1.6, 70, { auto: true, spread: .008 }],
  ['Plasma rifle', 'PLASMAR', 'Rifle', 30, 8, 75, 40, 200, 2, 65, { auto: true, splash: { radius: 1.5, damage: 6 } }],
  ['Pump shotgun', 'PUMP', 'Shotgun', 7, 9, 800, 6, 36, 2.8, 25, { pellets: 8, spread: .075, falloff: [6, 25, .15] }],
  ['Sawed-off', 'SAWED', 'Shotgun', 15, 8, 600, 2, 24, 2.2, 18, { pellets: 10, spread: .12, falloff: [4, 18, .1] }],
  ['Slug gun', 'SLUG', 'Shotgun', 17, 60, 1000, 5, 30, 3, 70, { headshotMultiplier: 1.5 }],
  ['Combat shotgun', 'COMBAT', 'Shotgun', 21, 6, 380, 8, 48, 3, 28, { auto: true, pellets: 6, spread: .07, falloff: [6, 28, .15] }],
  ['Flak cannon', 'FLAK', 'Shotgun', 28, 7, 1100, 4, 24, 3.2, 40, { pellets: 6, spread: .06, splash: { radius: 3, damage: 12 } }],
  ['Scatter blaster', 'SCATTER', 'Shotgun', 33, 5, 700, 6, 36, 2.6, 22, { pellets: 14, spread: .15, falloff: [3, 22, .08] }],
  ['Light machine gun', 'LMG', 'LMG', 12, 8, 85, 100, 400, 4, 70, { auto: true, spread: .02, moveMult: .9 }],
  ['Squad gun', 'SQUAD', 'LMG', 19, 10, 100, 60, 240, 4.2, 75, { auto: true, spread: .015, moveMult: .9 }],
  ['Minigun', 'MINIGUN', 'LMG', 25, 5, 40, 200, 600, 6, 55, { auto: true, spread: .045, moveMult: .75 }],
  ['Heavy machine gun', 'HMG', 'LMG', 31, 13, 120, 50, 200, 4.5, 80, { auto: true, moveMult: .8 }],
  ['Marksman rifle', 'MARKSMAN', 'Marksman', 8, 28, 400, 10, 50, 2.6, 130, { zoom: 40, headshotMultiplier: 2 }],
  ['DMR', 'DMR', 'Marksman', 13, 22, 250, 15, 75, 2.4, 110, { zoom: 45, headshotMultiplier: 1.8 }],
  ['Bolt sniper', 'BOLT', 'Marksman', 16, 90, 1200, 4, 20, 4, 450, { zoom: 14, headshotMultiplier: 2 }],
  ['Ghost sniper', 'GHOST', 'Marksman', 22, 55, 650, 6, 30, 3.2, 350, { zoom: 18, headshotMultiplier: 2 }],
  ['Anti-materiel rifle', 'AMR', 'Marksman', 36, 120, 1800, 3, 12, 5, 500, { zoom: 12, pierce: 2, moveMult: .85, headshotMultiplier: 1.8 }],
  ['Rail rifle', 'RAIL', 'Marksman', 40, 70, 1000, 6, 24, 3.5, 400, { zoom: 16, pierce: 3, headshotMultiplier: 1.3 }],
  ['Grenade launcher', 'GRENADE', 'Launcher', 14, 45, 1200, 6, 24, 3.2, 120, { splash: { radius: 5, damage: 80 }, headshotMultiplier: 1 }],
  ['Mini-rocket pod', 'PODS', 'Launcher', 23, 20, 350, 8, 32, 3.5, 150, { splash: { radius: 3, damage: 40 }, headshotMultiplier: 1 }],
  ['Napalm launcher', 'NAPALM', 'Launcher', 29, 30, 1600, 3, 12, 4, 110, { splash: { radius: 6, damage: 40 }, burn: { dps: 10, secs: 4 }, headshotMultiplier: 1 }],
  ['Mortar', 'MORTAR', 'Launcher', 34, 60, 2500, 1, 8, 5, 200, { splash: { radius: 9, damage: 85 }, headshotMultiplier: 1, moveMult: .9 }],
  ['Cluster launcher', 'CLUSTER', 'Launcher', 41, 28, 2000, 2, 10, 4, 160, { pellets: 3, spread: .06, splash: { radius: 6, damage: 25 }, headshotMultiplier: 1 }],
  ['Nova cannon', 'NOVA', 'Launcher', 48, 110, 3000, 1, 4, 6, 250, { splash: { radius: 12, damage: 110 }, headshotMultiplier: 1, moveMult: .85 }],
  ['Laser rifle', 'LASER', 'Energy', 10, 5, 30, 100, 300, 2.5, 60, { auto: true }],
  ['Flamethrower', 'FLAME', 'Energy', 20, 4, 50, 150, 450, 3, 14, { auto: true, spread: .08, falloff: [4, 14, .3], burn: { dps: 8, secs: 3 }, moveMult: .95 }],
  ['Arc caster', 'ARC', 'Energy', 27, 14, 100, 30, 120, 2, 40, { auto: true, spread: .03, burn: { dps: 4, secs: 2 } }],
  ['Toxin sprayer', 'TOXIN', 'Energy', 29, 2, 60, 100, 300, 3, 16, { auto: true, spread: .06, burn: { dps: 6, secs: 5 } }],
  ['Inferno gun', 'INFERNO', 'Energy', 32, 6, 45, 120, 360, 3, 18, { auto: true, spread: .07, falloff: [5, 18, .3], burn: { dps: 12, secs: 3 } }],
  ['Thunder cannon', 'THUNDER', 'Energy', 35, 14, 900, 5, 25, 3, 45, { pellets: 5, spread: .08, splash: { radius: 2, damage: 12 } }],
  ['Void blaster', 'VOID', 'Energy', 38, 12, 150, 20, 100, 2, 60, { auto: true, lifesteal: .4 }],
  ['Death ray', 'DEATHRAY', 'Energy', 45, 3, 20, 300, 900, 5, 50, { auto: true, moveMult: .85 }],
  ['Singularity gun', 'SINGULAR', 'Energy', 50, 90, 2500, 1, 5, 5, 200, { splash: { radius: 14, damage: 85 }, headshotMultiplier: 1 }]
];
const WEAPONS = (() => {
  const list = BASE_WEAPONS.map((w, i) => ({ ...w, cls: ['Rifle', 'Marksman', 'Launcher'][i], ...(i === 1 ? { zoom: 18 } : {}), ...(i === 2 ? { pickupOnly: true } : {}) }));   // the rocket launcher is never in a loadout: it lies in a hidden spot on each map
  for (const [name, short, cls, lv, dmg, rate, mag, max, rel, rng, o] of ROWS) list.push({ name, short, cls, damage: dmg, headshotMultiplier: 1.5, fireRateDelay: rate, magazineSize: mag, maxAmmo: max, reloadTime: rel, range: rng, unlockLevel: lv, auto: false, len: LEN[cls], ...o });
  return list;
})();
const POWER = WEAPONS.map((w, i) => i).filter(i => ['Marksman', 'Launcher', 'Energy', 'LMG', 'Shotgun'].includes(WEAPONS[i].cls) && !WEAPONS[i].pickupOnly);   // what the map's weapon pickups hand out: a different power weapon every match (the rocket launcher has its own fixed pickup)
const ROCKET = WEAPONS.findIndex(w => w.pickupOnly);
const DEFAULT_LOADOUT = [0, 1, 3];   // assault rifle, sniper rifle, pistol
const cleanLoadout = a => {   // three valid weapon numbers; a pickup-only weapon (the rocket launcher) that an old profile still carries is swapped for a pistol, or the next free starter weapon
  if (!(Array.isArray(a) && a.length === 3 && a.every(i => Number.isInteger(i) && i >= 0 && i < WEAPONS.length))) return DEFAULT_LOADOUT.slice();
  const out = a.slice(); out.forEach((i, k) => { if (WEAPONS[i].pickupOnly) out[k] = [3, 9, 4, 0].find(j => !out.includes(j)); });
  return out;
};
const loadoutOf = p => p.bot ? p.loadout : cleanLoadout(profOf(p).eq.loadout).map(i => lvOf(p) >= WEAPONS[i].unlockLevel ? i : 0);   // the three weapons on keys 1-3
const BOT_LEVEL = 10;   // whatever level a bot pretends to be, it only carries guns a level 10 player could use; anything better it has to find on the map
function botLoadout() {   // one weapon for the middle, one for close in, one for long range, all from the level 10 list
  const pool = cls => { const a = WEAPONS.map((w, i) => i).filter(i => cls.includes(WEAPONS[i].cls) && WEAPONS[i].unlockLevel <= BOT_LEVEL && !WEAPONS[i].pickupOnly); return a.length ? randOf(a) : 0; };
  return [pool(['Rifle', 'LMG', 'Energy']), pool(['Pistol', 'SMG', 'Shotgun']), pool(['Marksman', 'Launcher'])];
}
const spreadDir = (d, s) => { const x = d.x + (Math.random() - .5) * 2 * s, y = d.y + (Math.random() - .5) * 2 * s, z = d.z + (Math.random() - .5) * 2 * s, l = Math.hypot(x, y, z); return { x: x / l, y: y / l, z: z / l }; };
const falloffMul = (w, d) => { const [a, b, m] = w.falloff; return d <= a ? 1 : d >= b ? m : 1 - (1 - m) * (d - a) / (b - a); };   // shotguns and flamers lose power with range
function rayShot(me, o, dir, w) {   // one ray of a shot: damage, piercing through targets, and the distance travelled (for the tracer)
  let oo = o, t = 0, left = w.range;
  for (let hop = 0; hop <= (w.pierce || 0); hop++) {
    const hit = cast(me, oo, dir, left); t += hit.t; applyHit(me, hit, oo, dir, w, t);
    if (!hit.who) break;
    oo = { x: oo.x + dir.x * (hit.t + .8), y: oo.y + dir.y * (hit.t + .8), z: oo.z + dir.z * (hit.t + .8) }; t += .8; left -= hit.t + .8; if (left <= 0) break;
  }
  return t;
}

// ---- maps ----
// A map is plain data. The server sends it to every player and each browser builds the scene from it.
//   blocks     solid boxes: x/z centre, hx/hz half-sizes, h height, y bottom (default 0), kind = how it looks
//              (rock, cliff, mesa, mound, spire, tree, pine, cactus, crate, wall, building, platform, deck, ceiling). You can stand on top, bump your head underneath, never walk through.
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

// ---- The five maps. Every one covers the same 360,000 square metres (the old 600 x 600) but in a different shape, with the two team bases in different places:
//   Twin Citadels   a cross              bases at the ends of the north and south arms
//   Emerald Valley  a long valley        750 x 480, bases at the two far ends
//   Glacier Run     a circular island    bases at the north and south edges
//   Sunbaked Canyons an L shape          bases at the end of each arm
//   Moonrise Craters a ring round a crater peak, bases on opposite sides
// Each is generated from a fixed seed, so every server builds exactly the same map. Tall cliff walls follow the edge of the shape, so you can see it from inside.
// Natural kinds: rock (boulder), cliff (long ridge or edge wall), mesa (flat-topped plateau, climbed by its ramps), mound (low hill or dune), spire (tall rock needle: the tallest carry gun nests),
// tree / pine / cactus (solid trunks). The bases are sci-fi walls (wall, building, platform, crate).
const MAPS = {};
const BH = 48;   // the edge walls are as high as a helicopter can fly (the ceiling is 4 m above its top altitude)
const SHAPES = {   // each gives the playable outline: inside(x, z), its bounding box (ex, ez), the world bounds (bx, bz), and the edge to wall off (straight edges and/or circles)
  cross: () => { const a = 146.75, E = 380; return { ex: E, ez: E, bx: E + 14, bz: E + 14, inside: (x, z) => (Math.abs(x) <= a && Math.abs(z) <= E) || (Math.abs(z) <= a && Math.abs(x) <= E),
    edges: [[-a, E, a, E], [a, E, a, a], [a, a, E, a], [E, a, E, -a], [E, -a, a, -a], [a, -a, a, -E], [a, -E, -a, -E], [-a, -E, -a, -a], [-a, -a, -E, -a], [-E, -a, -E, a], [-E, a, -a, a], [-a, a, -a, E]] }; },
  rect: () => { const X = 375, Z = 240; return { ex: X, ez: Z, bx: X + 14, bz: Z + 14, inside: (x, z) => Math.abs(x) <= X && Math.abs(z) <= Z, edges: [[-X, Z, X, Z], [X, Z, X, -Z], [X, -Z, -X, -Z], [-X, -Z, -X, Z]] }; },
  disc: () => { const r = 341; return { ex: r, ez: r, bx: r + 30, bz: r + 30, inside: (x, z) => Math.hypot(x, z) <= r, rings: [[0, 0, r, 'out']] }; },
  L: () => { const E = 325, N = 75; return { ex: E, ez: E, bx: E + 14, bz: E + 14, inside: (x, z) => (x >= -E && x <= N && Math.abs(z) <= E) || (z >= -E && z <= N && Math.abs(x) <= E),
    edges: [[-E, E, N, E], [N, E, N, N], [N, N, E, N], [E, N, E, -E], [E, -E, -E, -E], [-E, -E, -E, E]] }; },
  ring: () => { const r = 363, h = 119.5; return { ex: r, ez: r, bx: r + 30, bz: r + 30, inside: (x, z) => { const d = Math.hypot(x, z); return d <= r && d >= h; }, rings: [[0, 0, r, 'out'], [0, 0, h, 'in']] }; }
};
function buildWild(c) {
  let seed = c.seed; const R = () => (seed = (seed * 16807) % 2147483647) / 2147483647, between = (a, b) => a + (b - a) * R();
  const S = SHAPES[c.shape](), AF = 4 * S.ex * S.ez / 360000, rep = n => Math.round(n * AF);   // bigger bounding boxes waste more tries on ground outside the shape, so they get more tries
  const rx = () => between(-S.ex + 10, S.ex - 10), rz = () => between(-S.ez + 10, S.ez - 10);
  const blocks = [], ramps = [], bases = [], spawns = { ffa: [], vanguard: [], horizon: [] }, vehicles = [], pickups = [], turrets = [], frames = [];
  const free = (x, z, hx, hz, pad = 2.5, skip = null) => !blocks.some(o => o !== skip && Math.abs(x - o.x) < hx + o.hx + pad && Math.abs(z - o.z) < hz + o.hz + pad) && !ramps.some(r => Math.abs(x - r.x) < hx + r.hx + pad && Math.abs(z - r.z) < hz + r.hz + pad);
  const keep = (x, z, hx, hz) => frames.some(f => { const z0 = f.ax === 'z', u = z0 ? x - f.lat : z - f.lat, d = z0 ? f.back - f.sign * z : f.back - f.sign * x, hu = z0 ? hx : hz, hd = z0 ? hz : hx; return Math.abs(u) - hu < 94 && d - hd < 152; });   // each base and the open ground in front of its gate stays clear of landscape
  const fits = (x, z, hx, hz) => [[1, 1], [1, -1], [-1, 1], [-1, -1]].every(([a, b]) => S.inside(x + a * (hx + 6), z + b * (hz + 6)));   // inside the shape, with a 6 m margin to the edge wall
  const add = (x, z, hx, hz, h, kind, y = 0) => { const b = B(rd(x), rd(z), rd(hx), rd(hz), rd(h), kind, rd(y)); blocks.push(b); return b; };
  const put = (x, z, hx, hz, h, kind, y = 0, pad = 2.5) => !keep(x, z, hx, hz) && fits(x, z, hx, hz) && free(x, z, hx, hz, pad) ? add(x, z, hx, hz, h, kind, y) : null;
  const lean = (b, side, len, wid) => {   // a natural ramp up one face of a block. It climbs toward the block and ends flush with its top
    const y0 = b.y || 0, y1 = y0 + b.h;
    const r = { S: () => RAMP(b.x, b.z + b.hz + len / 2, wid, len / 2, y0, y1, 'N'), N: () => RAMP(b.x, b.z - b.hz - len / 2, wid, len / 2, y0, y1, 'S'), E: () => RAMP(b.x + b.hx + len / 2, b.z, len / 2, wid, y0, y1, 'W'), W: () => RAMP(b.x - b.hx - len / 2, b.z, len / 2, wid, y0, y1, 'E') }[side]();
    if (keep(r.x, r.z, r.hx, r.hz) || !fits(r.x, r.z, r.hx, r.hz) || !free(r.x, r.z, r.hx, r.hz, 1, b)) return false;
    for (const k of ['x', 'z', 'hx', 'hz', 'y0', 'y1']) r[k] = rd(r[k]);
    r.nat = 1; ramps.push(r); return true;
  };
  // A base is written once in its own coordinates (u across, d = metres in from its back wall) and placed wherever the map wants it: `ax` is the axis it points along, `sign` which end, `back` how far
  // out the back wall is, `lat` how far off centre. `t` marks a block as a team's, which the browser lights up.
  const addBase = (team, ax, sign, back, lat) => {
    frames.push({ ax, sign, back, lat }); const zz = ax === 'z';
    const P = (u, d) => zz ? [lat + u, sign * (back - d)] : [sign * (back - d), lat + u];
    const out = zz ? (sign > 0 ? 'S' : 'N') : (sign > 0 ? 'E' : 'W'), inn = { N: 'S', S: 'N', E: 'W', W: 'E' }[out], vy = zz ? (sign > 0 ? 0 : Math.PI) : (sign > 0 ? Math.PI / 2 : -Math.PI / 2);   // yaw 0 looks along -Z
    const W = (u, d, hu, hd, h, kind = 'wall', y = 0) => { const [x, z] = P(u, d), b = add(x, z, zz ? hu : hd, zz ? hd : hu, h, kind, y); b.t = team; return b; };
    const RP = (u, d, hu, hd, y0, y1, dir) => { const [x, z] = P(u, d); return RAMP(x, z, zz ? hu : hd, zz ? hd : hu, y0, y1, dir); };
    W(0, 2, 80, 2, 14); W(-78, 61, 2, 57, 12); W(78, 61, 2, 57, 12); W(-47, 118, 33, 2, 12); W(47, 118, 33, 2, 12);   // back, side and front walls; the gate is the 28 m gap in the front wall
    W(-36, 82, 22, 1.5, 6); W(36, 82, 22, 1.5, 6);                                                                     // an inner defensive line, also with a 28 m opening
    W(0, 40, 20, 8, 5, 'building'); ramps.push(RP(0, 60.5, 5, 12.5, 0, 5, out));                                      // the keep, with a ramp up to its roof; the spawns sit behind it
    for (const u of [-68, 68]) for (const d of [12, 108]) {                                                            // four sniper towers: a 14 m deck reached by a 35 m ramp
      W(u, d, 5, 5, 13.4, 'building'); W(u, d, 7, 7, .6, 'platform', 13.4);
      for (const [pu, pd, hu, hd] of [[0, -7, 7, .3], [0, 7, 7, .3], [-7, 0, .3, 7], [7, 0, .3, 7]]) if (pd !== (d === 12 ? 7 : -7)) W(u + pu, d + pd, hu, hd, 1.2, 'wall', 14);   // parapet, open where the ramp arrives
      ramps.push(d === 12 ? RP(u, 36.5, 3, 17.5, 0, 14, out) : RP(u, 83.5, 3, 17.5, 0, 14, inn));
      if (u === -68 && d === 12) { const [x, z] = P(u, d); pickups.push({ wi: 1, x: rd(x), y: 15.2, z: rd(z) }); }   // one weapon on the deck of one tower in each base
    }
    for (let i = 0; i < 10; i++) { const u = between(-60, 60), d = between(52, 112), [x, z] = P(u, d); if (Math.abs(u) > 14 && !(d > 90 && Math.abs(Math.abs(u) - 30) < 8) && free(x, z, 1.5, 1.5)) add(x, z, 1.2, 1.2, 1.2, 'crate'); }   // loose cover in the yard, keeping the vehicle bays clear
    const [bx, bz] = P(0, 60); bases.push({ team, x: rd(bx), z: rd(bz), hx: zz ? 76 : 56, hz: zz ? 56 : 76 });
    const row = (d, n) => spawnRow(...P(-24, d), ...P(24, d), n).map(s => ({ ...s, yaw: rd(vy) })); spawns[team] = [...row(12, 8), ...row(20, 8)];
    const veh = (u, d, type, extra = {}) => { const [x, z] = P(u, d); vehicles.push({ x: rd(x), z: rd(z), yaw: rd(vy), type, ...extra }); };
    veh(-34, 100, 'car'); veh(34, 100, 'mech'); veh(0, 96, 'heli'); veh(26, 92, 'tank');   // a car, a mech, a helicopter and a tank in each base
    for (const u of [-17, 17]) { W(u, 110, 1.4, 1.4, TURRET.top, 'building'); const [x, z] = P(u, 110); turrets.push({ team, x: rd(x), y: TURRET.top, z: rd(z), r: TURRET.radius, h: TURRET.head }); veh(u, 110, 'turret', { y: TURRET.top, team, sentry: turrets.length }); }   // a sentry turret on top of a 14 m tower either side of the gate: high enough to see over the base walls; a teammate can take its gun seat (press E at the foot of the pedestal) and it stops firing by itself while someone is in it
  };
  for (const [team, ax, sign, back, lat] of c.bases) addBase(team, ax, sign, back, lat);
  // Hills with a power weapon on the first one: a three-step rocky hill, climbed by ramps.
  c.mounts.forEach(([cx, cz], k) => {
    [24, 16, 8].forEach((s, i) => { add(cx, cz, s, s, 2, 'mesa', i * 2); for (const d of [-1, 1]) ramps.push({ ...RAMP(cx, rd(cz + d * (s + 2.5)), 5, 2.5, i * 2, i * 2 + 2, d > 0 ? 'N' : 'S'), nat: 1 }); });
    ramps.push({ ...RAMP(rd(cx + 26.5), cz, 2.5, 5, 0, 2, 'W'), nat: 1 }, { ...RAMP(rd(cx - 26.5), cz, 2.5, 5, 0, 2, 'E'), nat: 1 });
    if (!k) pickups.push({ x: cx, y: 7.2, z: cz });
  });
  // The edge of the world: cliff walls the height of the helicopter ceiling all the way round the outline.
  const rimLine = (x0, z0, x1, z1) => {   // one straight edge: cliff blocks just outside it
    const horiz = z0 === z1, len = Math.abs(horiz ? x1 - x0 : z1 - z0), n = Math.max(1, Math.round(len / 30)), mx = (x0 + x1) / 2, mz = (z0 + z1) / 2;
    const nx = horiz ? 0 : (S.inside(mx - 10, mz) ? 1 : -1), nz = horiz ? (S.inside(mx, mz - 10) ? 1 : -1) : 0;   // the side that is not inside
    for (let i = 0; i < n; i++) { const t = (i + .5) / n, px = x0 + (x1 - x0) * t, pz = z0 + (z1 - z0) * t, hl = len / n / 2 + 7; if (horiz) add(px, z0 + nz * 7, hl, 7, between(BH - 4, BH), 'cliff'); else add(x0 + nx * 7, pz, 7, hl, between(BH - 4, BH), 'cliff'); }
  };
  const rimRing = (cx, cz, r, side) => { const rc = side === 'out' ? r + 14 : r - 14, n = Math.round(2 * Math.PI * rc / 18); for (let i = 0; i < n; i++) { const a = i / n * 6.2832; add(cx + rc * Math.cos(a), cz + rc * Math.sin(a), 14, 14, between(BH - 4, BH), 'cliff'); } };
  for (const e of S.edges || []) rimLine(...e);
  for (const r of S.rings || []) rimRing(...r);
  // ---- Landmarks and hideouts. Every map has its own set, built from axis-aligned boxes of the natural kinds and placed before the random scatter, so nothing random lands on top of them:
  //   archAt / henge   stone gateways, alone or four round a standing stone     tunnelRock   a rock massif with a tunnel through it     corridor   a long covered tunnel with side exits (they link the bases)
  //   skybridge        two flat-topped towers and a bridge you can walk under    crystals     clusters of tall needles     hideout   a walled nook with a screen rock before its opening, a weapon inside
  let DBG = false;   // MAPDEBUG=1 node server.js lists every landmark that had no room, and why
  const site = (x, z, hx, hz, pad = 3) => {   // is there room for something this big here?
    const k = keep(x, z, hx, hz), f = fits(x, z, hx, hz), fr = free(x, z, hx, hz, pad), ok = !k && f && fr;
    if (!ok && DBG) console.log('  [' + c.id + '] skipped a landmark at', x, z, 'size', hx, hz, k ? '(in a base zone)' : !f ? '(outside the shape)' : '(something is in the way)');
    return ok;
  };
  const far = (x, z, d) => bases.every(b => Math.hypot(x - b.x, z - b.z) > d);
  let landmarks = 0;
  const archAt = (x, z, ax, gap = 8, h = 9.5) => {   // a stone gateway you walk through along `ax`: two piers and a lintel
    const th = 2.2, ln = 3, big = gap / 2 + 2 * th; if (!site(x, z, ax === 'z' ? big : ln, ax === 'z' ? ln : big)) return false;
    if (ax === 'z') { for (const s of [-1, 1]) add(x + s * (gap / 2 + th), z, th, ln, h, 'cliff'); add(x, z, big, ln, 2.6, 'cliff', h - 2.6); }
    else { for (const s of [-1, 1]) add(x, z + s * (gap / 2 + th), ln, th, h, 'cliff'); add(x, z, ln, big, 2.6, 'cliff', h - 2.6); }
    landmarks++; return true;
  };
  const henge = (x, z, R0 = 19) => {   // a courtyard of four stone gateways round a standing stone, with a boulder at each corner
    if (!site(x, z, R0 + 9, R0 + 9)) return false;
    archAt(x, z - R0, 'z', 8, 10); archAt(x, z + R0, 'z', 8, 10); archAt(x - R0, z, 'x', 8, 10); archAt(x + R0, z, 'x', 8, 10);
    for (const [a, b] of [[1, 1], [1, -1], [-1, 1], [-1, -1]]) add(x + a * R0 * .72, z + b * R0 * .72, 1.7, 1.7, between(5, 7), 'rock');
    add(x, z, 1.6, 1.6, 4.4, 'rock'); return true;
  };
  const tunnelRock = (x, z, ax, len = 46, w = 7.5, h = 10, th = 7) => {   // a rock massif with a tunnel through it (you travel along `ax`); the passage is 6.4 m high
    const hx = ax === 'x' ? len / 2 : w / 2 + th, hz = ax === 'x' ? w / 2 + th : len / 2, pass = 6.4; if (!site(x, z, hx, hz)) return false;
    for (const s of [-1, 1]) { const o = s * (w / 2 + th / 2); if (ax === 'x') add(x, z + o, len / 2, th / 2, h, 'cliff'); else add(x + o, z, th / 2, len / 2, h, 'cliff'); }
    if (ax === 'x') add(x, z, len / 2, w / 2, h - pass, 'cliff', pass); else add(x, z, w / 2, len / 2, h - pass, 'cliff', pass);
    landmarks++; return true;
  };
  const corridor = (x0, z0, x1, z1, w = 7.5, every = 64) => {   // a long covered tunnel, 7.5 m wide and 6.4 m high, with a 9 m side exit every so often
    const ax = z0 === z1 ? 'x' : 'z', a0 = Math.min(ax === 'x' ? x0 : z0, ax === 'x' ? x1 : z1), a1 = Math.max(ax === 'x' ? x0 : z0, ax === 'x' ? x1 : z1), len = a1 - a0, mid = (a0 + a1) / 2;
    const cx = ax === 'x' ? mid : x0, cz = ax === 'x' ? z0 : mid, T = 1.6, H = 6.4, n = Math.max(2, Math.round(len / every)), seg = len / n, gap = 9;
    if (!site(cx, cz, ax === 'x' ? len / 2 : w / 2 + T, ax === 'x' ? w / 2 + T : len / 2)) return false;
    for (let i = 0; i < n; i++) {   // the side walls come in pieces, with an exit between each pair
      const s0 = a0 + i * seg + (i > 0 ? gap / 2 : 0), s1 = a0 + (i + 1) * seg - (i < n - 1 ? gap / 2 : 0), m = (s0 + s1) / 2, hl = (s1 - s0) / 2;
      for (const s of [-1, 1]) { const o = s * (w / 2 + T / 2); if (ax === 'x') add(m, cz + o, hl, T / 2, H, 'cliff'); else add(cx + o, m, T / 2, hl, H, 'cliff'); }
    }
    if (ax === 'x') add(cx, cz, len / 2, w / 2 + T, 1.8, 'mesa', H); else add(cx, cz, w / 2 + T, len / 2, 1.8, 'mesa', H);   // the roof
    landmarks++; return true;
  };
  const skybridge = (x, z, ax, span = 40, hg = 9) => {   // two flat-topped towers with a bridge between them; each tower has a long ramp up its outer side, and you can walk under the bridge
    const tw = 8, ramp = hg * 3.2, L = span / 2 + tw + ramp + 1; if (!site(x, z, ax === 'x' ? L : 9, ax === 'x' ? 9 : L)) return false;
    for (const s of [-1, 1]) {
      const tx = ax === 'x' ? x + s * span / 2 : x, tz = ax === 'x' ? z : z + s * span / 2; add(tx, tz, tw, tw, hg, 'mesa');
      const r = ax === 'x' ? RAMP(tx + s * (tw + ramp / 2), z, ramp / 2, 3.5, 0, hg, s > 0 ? 'W' : 'E') : RAMP(x, tz + s * (tw + ramp / 2), 3.5, ramp / 2, 0, hg, s > 0 ? 'N' : 'S');
      for (const k of ['x', 'z', 'hx', 'hz', 'y0', 'y1']) r[k] = rd(r[k]); r.nat = 1; ramps.push(r);
    }
    const dl = span / 2 - tw + 1; if (ax === 'x') { add(x, z, dl, 3, .8, 'mesa', hg - .8); for (const s of [-1, 1]) add(x, z + s * 2.75, dl - 1, .25, 1.1, 'cliff', hg); } else { add(x, z, 3, dl, .8, 'mesa', hg - .8); for (const s of [-1, 1]) add(x + s * 2.75, z, .25, dl - 1, 1.1, 'cliff', hg); }
    landmarks++; return true;
  };
  const crystals = (x, z, n = 7) => { for (let i = 0; i < n; i++) { const a = R() * 6.283, r = between(0, 5), cx = x + r * Math.cos(a), cz = z + r * Math.sin(a); if (!keep(cx, cz, 1, 1) && fits(cx, cz, 1, 1) && free(cx, cz, .8, .8, 1)) { const q = add(cx, cz, between(.6, 1.1), between(.6, 1.1), between(2.2, 6.5), 'crystal'); q.col = c.accent; } } };   // glassy needles in the map's accent colour
  const hideout = (x, z, face, roof) => {   // a walled nook, hard to see into: a back wall, two side walls, a front wall with a gap on one side, a screen boulder before the gap (and a roof when it is a cave)
    const vert = face === 'N' || face === 'S', sg = { N: -1, S: 1, E: 1, W: -1 }[face];   // sg: which way along its axis the opening looks
    const cx = vert ? x : x + sg * 10.2, cz = vert ? z + sg * 10.2 : z; if (!site(cx, cz, vert ? 8.6 : 11.8, vert ? 11.8 : 8.6, 2)) return null;
    const W = (u, d, hu, hd, h, kind = 'cliff', y = 0) => vert ? add(x + u, z + sg * d, hu, hd, h, kind, y) : add(x + sg * d, z + u, hd, hu, h, kind, y), wh = roof ? 6.8 : 6;   // u across, d out from the back wall
    W(0, 0, 8.1, 1.2, wh); W(-6.9, 5.5, 1.2, 5.5, wh); W(6.9, 5.5, 1.2, 5.5, wh); W(-3.9, 11, 3.9, 1.2, wh - .6); W(2.85, 20, 2.95, 1.5, 4.8, 'rock');   // the opening is 5.7 m wide and the screen boulder as wide, 6 m in front of it: bots can get round it too
    if (roof) W(0, 5.5, 8.1, 6.7, 1.8, 'cliff', 5);
    return { x: rd(vert ? x : x + sg * 4.5), z: rd(vert ? z + sg * 4.5 : z) };   // where the weapon lies
  };
  const PROG = {   // what each map gets; positions are in metres from the middle. A piece that has no room is simply skipped.
    field: () => { corridor(-205, -176, 205, -176); henge(-135, 176); henge(135, 176); tunnelRock(-80, -50, 'x', 46); tunnelRock(80, 50, 'x', 46); archAt(-165, 0, 'x', 9, 11); archAt(165, 0, 'x', 9, 11); archAt(0, -95, 'z', 9, 11); archAt(0, 95, 'z', 9, 11); },   // Emerald Valley: a root tunnel along the south flank, standing stones in the north, hollow hills in the middle
    glacier: () => { corridor(95, -160, 95, 160); skybridge(-140, 40, 'z'); skybridge(190, -120, 'z'); tunnelRock(-200, -40, 'z', 48); archAt(-60, -70, 'x', 8, 10); archAt(60, 70, 'x', 8, 10); archAt(0, -105, 'z', 9, 11); archAt(0, 105, 'z', 9, 11); },   // Glacier Run: an ice tunnel between the bases, two frozen sky bridges, an ice gate
    arena: () => { corridor(-60, -125, 150, -125); corridor(-125, -60, -125, 150); skybridge(-250, -215, 'x'); skybridge(-30, -35, 'z'); tunnelRock(-120, -255, 'x', 64, 8, 11); tunnelRock(30, -230, 'z', 56, 8, 11); archAt(-250, 40, 'z', 10, 12); archAt(60, -170, 'x', 10, 12); archAt(150, -60, 'x', 10, 12); archAt(-230, 150, 'z', 10, 12); },   // Sunbaked Canyons: two tunnels from the elbow to the bases, natural bridges, hollow mesas, sandstone arches
    station: () => { corridor(-175, -170, -175, 170); corridor(175, -170, 175, 170); skybridge(-215, -150, 'z'); skybridge(215, 150, 'z'); archAt(-140, -255, 'x', 9, 12); archAt(140, 255, 'x', 9, 12); archAt(140, -255, 'x', 9, 12); archAt(-140, 255, 'x', 9, 12); tunnelRock(0, 0 + 160, 'x', 50, 8, 11); },   // Moonrise Craters: twin lava tubes joining the bases, bridges over the craters, monolith gates
    frontier: () => { corridor(95, -210, 95, 210); corridor(-95, -210, -95, 210); for (const x of [175, 215, 255]) { archAt(x, 0, 'x', 9, 10); archAt(-x, 0, 'x', 9, 10); } henge(320, 0); henge(-320, 0); skybridge(0, -190, 'x'); skybridge(0, 190, 'x'); },   // Twin Citadels: a pair of metro tunnels between the citadels, an avenue of arches down each arm, a henge at each end
  };
  DBG = !!process.env.MAPDEBUG; (PROG[c.id] || (() => {}))(); DBG = false;
  for (let i = 0; i < (c.crystals || 0); i++) crystals(rx(), rz());
  const HIDE = c.hideouts == null ? 5 : c.hideouts, roofP = c.caves == null ? .3 : c.caves, spots = [];
  for (let t = 0; t < 5000 && spots.length < HIDE; t++) {   // hideouts: far from the bases and from each other, never on a hill
    const x = rx(), z = rz(), face = 'NSEW'[Math.floor(R() * 4)];
    if (!far(x, z, 100) || c.mounts.some(([a, b2]) => Math.hypot(x - a, z - b2) < 60) || spots.some(q => Math.hypot(q.x - x, q.z - z) < 110)) continue;
    const h = hideout(x, z, face, R() < roofP); if (h) spots.push(h);
  }
  { const mid = c.mounts[c.mid || 0]; spots.sort((a, b2) => Math.abs(Math.hypot(a.x - mid[0], a.z - mid[1]) - 120) - Math.abs(Math.hypot(b2.x - mid[0], b2.z - mid[1]) - 120));   // the rocket launcher goes in the hideout about 120 m from the middle: worth a trip, not a gift
    spots.forEach((q, i) => pickups.push(i === 0 ? { fixed: ROCKET, x: q.x, y: 1.2, z: q.z } : { x: q.x, y: 1.2, z: q.z })); }
  // Landscape pieces. Each one only goes down where there is room, so a failed try just leaves open ground.
  const mesa = (x, z, big) => {   // a flat-topped plateau reached by up to two long ramps
    const hx = big ? between(14, 24) : between(9, 17), hz = big ? between(12, 20) : between(8, 14), h = Math.round(between(4, 8) * 2) / 2, b = put(x, z, hx, hz, h, 'mesa', 0, 9); if (!b) return false;
    const s0 = Math.floor(R() * 4); let n = 0;
    for (let i = 0; i < 4 && n < 2; i++) if (lean(b, 'NSEW'[(s0 + i) % 4], h * 3.2, 3.5)) n++;
    if (!n) { blocks.pop(); return false; }
    return true;
  };
  const mound = (x, z) => {   // a low hill or dune you can run straight over
    const f = R() < .5, a = between(8, 14), s = between(5, 9), h = between(1.4, 2.6), b = put(x, z, f ? s : a, f ? a : s, h, 'mound', 0, 5); if (!b) return false;
    let n = 0; for (const side of f ? 'NS' : 'EW') if (lean(b, side, h * 3.4, s * .7)) n++;
    if (!n) { blocks.pop(); return false; }
    return true;
  };
  const outcrop = (x, z) => {   // a boulder, sometimes with another on top or beside it
    const s = between(1.6, 3.6), h = between(1.8, 4.4), b = put(x, z, s, s * between(.7, 1.3), h, 'rock', 0, 3); if (!b) return;
    if (s > 2.2 && R() < .5) add(b.x + between(-.6, .6), b.z + between(-.6, .6), b.hx * .55, b.hz * .55, h * .6, 'rock', h);
    if (R() < .5) put(x + (R() < .5 ? -1 : 1) * (s + between(1, 2)), z + between(-2, 2), between(.8, 1.4), between(.8, 1.4), between(1, 2), 'rock', 0, .8);
  };
  const ridge = (x, z) => { const f = R() < .5, len = between(14, 34), t = between(1.6, 2.8); put(x, z, f ? t : len / 2, f ? len / 2 : t, between(4.5, 8.5), 'cliff', 0, 4); };
  const canyon = (cx, cz) => {   // two cliff walls with gaps, a lane between them, and boulders to hide behind
    const f = R() < .5, ax = f ? 12 : 27, az = f ? 27 : 12; if (keep(cx, cz, ax, az) || !fits(cx, cz, ax, az)) return;
    for (const s of [-1, 1]) for (const [a, e] of [[-26, -10], [-6, 8], [12, 26]]) { const m = (a + e) / 2, hl = (e - a) / 2; put(f ? cx + s * 9 : cx + m, f ? cz + m : cz + s * 9, f ? 2.2 : hl, f ? hl : 2.2, between(5, 8.5), 'cliff', 0, 1); }
    for (let i = 0; i < 4; i++) { const t = between(-20, 20), o = between(-4, 4); put(f ? cx + o : cx + t, f ? cz + t : cz + o, 1.2, 1.2, between(1.2, 2.2), 'rock', 0, 1.5); }
  };
  const crater = (cx, cz, r) => {   // a ring of rock with two gaps to get in by, and a few boulders inside
    if (keep(cx, cz, r + 4, r + 4) || !fits(cx, cz, r + 4, r + 4) || !free(cx, cz, r + 3, r + 3, 2)) return;
    const n = Math.round(Math.PI * 2 * r / 5.4), ph = R() * 6.283;
    for (let i = 0; i < n; i++) { const a = i / n * 6.283; if (Math.cos(2 * a + ph) > .8) continue; add(cx + r * Math.cos(a), cz + r * Math.sin(a), 2.6, 2.6, between(1.8, 3.4), 'rock'); }
    for (let i = 0; i < 3; i++) put(cx + between(-r * .5, r * .5), cz + between(-r * .5, r * .5), 1.2, 1.2, between(1, 1.8), 'rock', 0, 1.5);
  };
  const spire = (x, z, h) => put(x, z, 1.3, 1.3, h, 'spire', 0, 3.5);
  const diag = (x0, z0, x1, z1) => {   // a jagged ridge running corner to corner, with openings to get through
    const n = Math.round(Math.hypot(x1 - x0, z1 - z0) / 9);
    for (let i = 0; i <= n; i++) { if (i % 7 === 3 || i % 7 === 4) continue; const t = i / n; put(x0 + (x1 - x0) * t + between(-1.5, 1.5), z0 + (z1 - z0) * t + between(-1.5, 1.5), between(3.5, 5), between(3.5, 5), between(5, 9), 'cliff', 0, -2); }
  };
  const ruin = (x, z) => {   // four broken walls round an old courtyard, open at the corners, with a standing stone in the middle
    const hl = between(5, 8), g = hl + 3, h = between(2.8, 4);
    if (keep(x, z, g + 2, g + 2) || !fits(x, z, g + 2, g + 2) || !free(x, z, g + 1, g + 1, 2)) return;
    add(x, z - g, hl, .9, h, 'cliff'); add(x, z + g, hl, .9, h * .8, 'cliff'); add(x - g, z, .9, hl, h * .9, 'cliff'); add(x + g, z, .9, hl, h * 1.1, 'cliff'); add(x, z, 1.4, 1.4, h * 1.4, 'rock');
  };
  const grove = (x, z) => { const [kind, hx, h0, h1, n] = c.tree; for (let i = 0; i < n; i++) put(x + between(-16, 16), z + between(-16, 16), hx, hx, between(h0, h1), kind, 0, 3.2); };
  for (const [sx, sz] of c.nests) for (let t = 0; t < 80; t++) if (spire(sx + between(-25, 25), sz + between(-25, 25), 15)) break;   // the four tallest spires carry gun nests (added below)
  if (c.valley) for (const s of [-1, 1]) for (let x0 = -S.ex + 20; x0 < S.ex - 60; x0 += 84) put(x0 + 32 + between(-4, 4), s * 114 + between(-5, 5), 32, between(4, 6), between(15, 21), 'cliff', 0, 1);   // sheer valley walls along both sides, with passes through
  if (c.diag) { diag(-215, -135, 215, 135); diag(-215, 135, 215, -135); }   // two ice ridges crossing in the middle
  if (c.grid) for (let gx = -300; gx <= 300; gx += 115) for (let gz = -300; gz <= 300; gz += 115) mesa(gx + between(-12, 12), gz + between(-12, 12), true);   // canyon country: a grid of big mesas with lanes between them
  for (let i = 0, n = 0; n < c.mesas && i < 160; i++) if (mesa(rx(), rz())) n++;
  for (let i = 0; i < rep(c.ruins || 0); i++) ruin(rx(), rz());
  for (let i = 0; i < rep(c.canyons); i++) canyon(rx(), rz());
  for (let i = 0; i < rep(c.craters || 0); i++) crater(rx(), rz(), between(16, 28));
  for (let i = 0; i < rep(c.groves); i++) grove(rx(), rz());
  for (let i = 0, n = 0; n < c.mounds && i < c.mounds * 10; i++) if (mound(rx(), rz())) n++;
  for (let i = 0; i < rep(c.ridges); i++) ridge(rx(), rz());
  for (let i = 0; i < rep(c.spires); i++) spire(rx(), rz(), Math.round(between(8, 13)));
  for (let i = 0; i < rep(c.rocks); i++) outcrop(rx(), rz());
  for (let i = 0; i < rep(c.low); i++) put(rx(), rz(), between(.7, 1.5), between(.7, 1.5), between(.8, 1.5), 'rock', 0, 2);   // low boulders: cover you have to jump
  const [mx0, mz0] = c.mounts[0], farFromBases = (x, z, d) => bases.every(b => Math.hypot(x - b.x, z - b.z) > d);
  for (let i = 0, n = 0; n < 2 && i < 200; i++) { const x = mx0 + between(-150, 150), z = mz0 + between(-150, 150); if (fits(x, z, 3, 4) && c.mounts.every(([a, b]) => Math.hypot(x - a, z - b) > 45) && farFromBases(x, z, 120) && free(x, z, 3, 4, 4)) { vehicles.push({ x: rd(x), z: rd(z), yaw: rd(between(-3, 3)), type: 'car' }); n++; } }   // two spare cars in the field
  for (let t = 0; spawns.ffa.length < 20 && t < 6000; t++) { const x = rd(rx()), z = rd(rz()); if (fits(x, z, 3, 3) && !keep(x, z, 3, 3) && free(x, z, 1, 1, 3) && spawns.ffa.every(s => Math.hypot(s.x - x, s.z - z) > 40)) spawns.ffa.push(at(x, 0, z, c.mounts[0])); }
  return {
    id: c.id, name: c.name, half: Math.max(S.bx, S.bz), ex: S.bx, ez: S.bz, centre: c.mounts[c.mid || 0], theme: c.theme, sky: c.sky, fog: c.fog || [170, 720], sun: true, big: true, ceiling: 0, lights: [], tint: c.tint, accent: c.accent, stars: !!c.stars,
    ground: 0, bounds: { min: [-S.bx, -2, -S.bz], max: [S.bx, BH, S.bz], edge: 'wall' }, killZones: [], blocks, ramps, bases, spawns, vehicles, pickups, turrets, info: { landmarks, hideouts: spots.length }
  };
}
for (const c of [   // five very different places, each its own shape: a misty forest valley, a frozen island, canyon country, a cratered moon ring, and open grassland with ruins in a cross
  { id: 'field',    name: 'Emerald Valley',   theme: 'forest', shape: 'rect', sky: 0xbfe0d2, tint: 0xd9e4de, accent: 0x7ee8a8, fog: [70, 420], seed: 20261101, valley: true, caves: .25, mesas: 0, mounds: 6,  canyons: 0, ridges: 4, rocks: 70,  low: 120, groves: 26, tree: ['tree', .9, 10, 15, 9], spires: 3,
    bases: [['vanguard', 'x', -1, 371, 0], ['horizon', 'x', 1, 371, 0]], mounts: [[0, 0]], nests: [[-150, 175], [150, -175], [-150, -175], [150, 175]] },
  { id: 'glacier',  name: 'Glacier Run',      theme: 'ice',    shape: 'disc', sky: 0xe6f6ff, tint: 0xeaf4fb, accent: 0x6fd3ff, seed: 20261102, diag: true, caves: .9, crystals: 16, mesas: 4, mounds: 8,  canyons: 0, ridges: 5, rocks: 90,  low: 120, groves: 8,  tree: ['pine', .7, 9, 13, 7],   spires: 9,
    bases: [['vanguard', 'z', -1, 316, 0], ['horizon', 'z', 1, 316, 0]], mounts: [[0, 0]], nests: [[-230, 60], [230, -60], [-95, -125], [95, 125]] },
  { id: 'arena',    name: 'Sunbaked Canyons', theme: 'desert', shape: 'L',    sky: 0xffd27f, tint: 0xe3c196, accent: 0xff9a4d, seed: 20261103, grid: true, caves: .15, mesas: 0, mounds: 12, canyons: 3, ridges: 3, rocks: 80,  low: 130, groves: 6,  tree: ['cactus', .6, 3, 5, 3], spires: 4,
    bases: [['vanguard', 'z', 1, 321, -125], ['horizon', 'x', 1, 321, -125]], mounts: [[-125, -125]], nests: [[-270, 150], [40, 225], [150, -270], [235, 35]] },
  { id: 'station',  name: 'Moonrise Craters', theme: 'moon',   shape: 'ring', sky: 0x1f2d66, tint: 0xb4bdd6, accent: 0xb48cff, seed: 20261104, stars: true, caves: .8, crystals: 10, mesas: 4, mounds: 6,  canyons: 3, ridges: 9, rocks: 140, low: 160, groves: 0,  tree: ['tree', .8, 7, 11, 0],   spires: 6, craters: 9,
    bases: [['vanguard', 'z', -1, 334, 0], ['horizon', 'z', 1, 334, 0]], mounts: [[245, 0], [-245, 0]], nests: [[-200, 140], [200, -140], [-210, -110], [210, 110]] },
  { id: 'frontier', name: 'Twin Citadels',    theme: 'grass',  shape: 'cross', sky: 0xc2e7ff, tint: 0xdde5ec, accent: 0x7ec8ff, seed: 20261013, caves: .25, mesas: 2, mounds: 22, canyons: 0, ridges: 3, rocks: 60,  low: 110, groves: 4,  tree: ['tree', .8, 7, 10, 5],   spires: 4, ruins: 9,
    bases: [['vanguard', 'z', -1, 376, 0], ['horizon', 'z', 1, 376, 0]], mounts: [[0, 0]], nests: [[-300, 20], [300, -20], [-110, -110], [110, 110]] }
]) MAPS[c.id] = buildWild(c);
for (const m of Object.values(MAPS)) {   // manned gun nests on top of the tallest rock spires (or pillars) of every map
  m.vehicles = m.vehicles || [];
  const pil = m.blocks.filter(b => b.kind === 'pillar' || b.kind === 'spire'), top = Math.max(0, ...pil.map(b => b.h));
  if (top >= 7) for (const b of pil) if (b.h === top) m.vehicles.push({ x: b.x, z: b.z, yaw: 0, type: 'turret', y: (b.y || 0) + b.h });
}
const vehDefs = m => m.vehicles.filter(d => !d.sentry || match.mode === 'tdm');   // the base sentries (and their gun seats) only exist in team deathmatch
const clientMap = m => { const { spawns, ...rest } = m; return { ...rest, vehicles: vehDefs(m) }; };   // players never need the spawn list

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
const matchInfo = () => ({ mode: match.mode, limit: LIMIT[match.mode], state: match.state, team: match.team, map: map.name, left: match.state === 'live' && match.endsAt ? Math.max(0, match.endsAt - Date.now()) : 0 });
const sendScores = () => emit('scores', { t: match.team, p: [...players.values()].map(p => [p.id, p.kills, p.deaths, lvOf(p)]) });
const vehRows = () => vehicles.map(v => [v.id, r2(v.x), r2(v.z), r3(v.yaw), v.driver ? v.driver.id : 0, r2(v.y || 0), v.gunner ? v.gunner.id : 0, VARM[v.type] ? Math.max(0, Math.round(100 * v.hp / VARM[v.type].hp)) : 100, v.dead ? 1 : 0]);   // ... then health as a percentage, and whether it is a wreck
function profileView(p) {
  const pr = profOf(p), lv = levelInfo(pr.xp);
  return { xp: pr.xp, level: lv.level, into: lv.into, need: lv.need, coins: pr.coins, kills: pr.kills, owned: pr.owned, eq: { ...pr.eq, loadout: cleanLoadout(pr.eq.loadout) }, st: statsFull(pr.st), save: sign(p.token, pr) };   // an old profile's rocket launcher is already swapped out here
}
const notice = (p, text, extra) => p.sock.emit('notice', { text, ...extra });
function grant(p, xp, coins, why, head) {
  if (p.bot) { p.prof.xp += xp; p.prof.coins += coins; return; }   // a bot's profile is a fake one: it earns coins on paper but is never saved   // XP and coins go to the player's saved profile; a level-up pays a bonus
  const pr = profOf(p), before = levelInfo(pr.xp).level;
  const mx = p.mx || (p.mx = { xp0: pr.xp, kills: 0, heads: 0, xp: 0, coins: 0, winCoins: 0, levelCoins: 0 });   // this match's takings: the results card at the end reads them (startMatch clears them)
  pr.xp += xp; pr.coins += coins; if (why === 'kill') { pr.kills++; mx.kills++; if (head) mx.heads++; }
  const up = levelInfo(pr.xp).level - before, bonus = up > 0 ? LEVEL_UP_COINS * up : 0;
  mx.xp += xp; mx.coins += coins + bonus; mx.levelCoins += bonus; if (why === 'win') mx.winCoins += coins;
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

// ---- counting the stats, and the public profile anyone in the room can open ----
const stOf = p => { if (!p || p.bot || !p.token) return null; const pr = profOf(p); return pr.st || (pr.st = {}); };   // bots and sentries have no saved profile: every stat call quietly skips them
const stat = (p, key, n = 1) => { const st = stOf(p); if (st) st[key] = statNum(st[key]) + n; };
const statSet = (p, key, v) => { const st = stOf(p); if (st) st[key] = v; };
const statMax = (p, key, v) => { const st = stOf(p); if (st && v > statNum(st[key])) st[key] = v; };
function saveProfile(p) {   // write the profile out and tell its owner: after something that pays no XP itself (a death, a lost match, a destroyed vehicle)
  if (!p || p.bot || !p.token || !p.sock) return;
  const pr = profOf(p); pr.rev++; store.set(p.token, pr); p.sock.emit('profile', profileView(p));
}
function killStats(k, v, head, how) {   // a kill: the victim's streak ends; the killer's streak, multi-kill chain and headshots count. Returns the awards to announce once the kill has been shown
  const awards = [], now = Date.now();
  v.streak = 0; v.multi = 0;
  if (!k || k === v) return awards;   // a fall, a splat on yourself: nobody scores
  k.streak = (k.streak || 0) + 1; k.multi = now - (k.lastKillAt || 0) < MULTI_MS ? (k.multi || 1) + 1 : 1; k.lastKillAt = now;
  if (k.bot || !k.token) return awards;
  if (head && !how) stat(k, 'headshots');
  statMax(k, 'bestStreak', k.streak);
  if (k.multi === 2) { stat(k, 'doubleKills'); awards.push('DOUBLE KILL'); }
  else if (k.multi === 3) { stat(k, 'tripleKills'); awards.push('TRIPLE KILL'); }
  const sk = STREAKS[k.streak]; if (sk) { stat(k, sk[0]); awards.push(sk[1]); }
  return awards;
}
function matchReport(p, win) {   // the end-of-match results card: what the match paid (kills and headshots are separate, 100 XP each) and where the level bar went
  const pr = profOf(p), mx = p.mx || { xp0: pr.xp, kills: 0, heads: 0, xp: 0, coins: 0, winCoins: 0, levelCoins: 0 }, from = levelInfo(mx.xp0), to = levelInfo(pr.xp);
  return { win: !!win, kills: mx.kills, heads: mx.heads, killXp: mx.kills * XP_PER_KILL, headXp: mx.heads * XP_PER_HEADSHOT, xp: mx.xp, coins: mx.coins, winCoins: mx.winCoins, levelCoins: mx.levelCoins, from, to, up: to.level - from.level };
}
const totalXp = L => 200 * (L - 1) + 50 * (L - 1) * L;   // XP needed to reach level L: the sum of xpToNext for every level before it
function botProfile(p) {   // bots have a profile too: believable numbers that follow their (fake) level, and are the same every time somebody looks
  let a = 0x811c9dc5; for (const ch of p.name + '|' + p.lv) { a ^= ch.charCodeAt(0); a = Math.imul(a, 16777619); }
  const rnd = () => { a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; };   // a small seeded random number generator
  const L = Math.max(1, p.lv || 1), xp = totalXp(L) + Math.floor(rnd() * xpToNext(L)), info = levelInfo(xp);
  const kills = Math.round(xp / XP_PER_KILL * (.9 + rnd() * .2)), kd = Math.min(3, .6 + Math.min(1.6, L / 40) * (.6 + rnd() * .8)), deaths = Math.round(kills / kd);
  const games = kills ? Math.max(1, Math.round(kills / (10 + rnd() * 8))) : 0, wins = Math.round(games * (.32 + rnd() * .2 + Math.min(.15, L / 500)));
  const dbl = Math.round(kills * (.03 + rnd() * .03)), tri = Math.round(dbl * (.08 + rnd() * .08)), sprees = Math.round(kills * (.06 + rnd() * .05)), dom = Math.floor(sprees * .5), unst = Math.floor(dom * .5), god = Math.floor(unst * .6);   // each rung is rarer, and a low-level bot has none of the top ones
  const best = god ? 10 + Math.floor(rnd() * 8) : unst ? 7 + Math.floor(rnd() * 3) : dom ? 5 + Math.floor(rnd() * 2) : sprees ? 3 + Math.floor(rnd() * 2) : Math.min(kills, 2);
  return { level: info.level, into: info.into, need: info.need, kills, st: statsFull({ deaths, games, wins, bestWinStreak: Math.min(wins, 1 + Math.floor(rnd() * 5)), vehKills: Math.round(kills * (.05 + rnd() * .1)), headshots: Math.round(kills * (.08 + rnd() * .15)), doubleKills: dbl, tripleKills: tri, sprees, dominating: dom, unstoppable: unst, godlike: god, bestStreak: best }) };
}
function pubProfile(p) {   // what any player in the room may see of another: name, level, look and stats
  const eq = profOf(p).eq, base = { id: p.id, name: p.name, faction: p.faction, eq: { body: eq.body, weapon: eq.weapon, frame: eq.frame } };
  if (p.bot) return { ...base, ...botProfile(p) };
  const pr = profOf(p), li = levelInfo(pr.xp);
  return { ...base, level: li.level, into: li.into, need: li.need, kills: pr.kills, st: statsFull(pr.st) };
}
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
  const sp = pickSpawn(p), loadout = loadoutOf(p);
  Object.assign(p, { x: sp.x, y: sp.y, z: sp.z, yaw: sp.yaw, pitch: 0, hp: maxHp(p), alive: true, loadout, wi: loadout[0], burnUntil: 0, ammos: WEAPONS.map(w => w.magazineSize), reserve: WEAPONS.map(w => w.maxAmmo), held: new Set(), reloadEnd: 0, nextShot: 0, vehicle: 0, epoch: p.epoch + 1, hist: [], vis: null, mem: null, hitBy: null });
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
  const c = Math.cos(v.yaw), s = Math.sin(v.yaw), limX = (map.ex || map.half) - BODY.r, limZ = (map.ez || map.half) - BODY.r;
  const solid = [...map.blocks.filter(groundBlock), ...map.ramps, ...map.killZones.map(k => ({ x: (k.min[0] + k.max[0]) / 2, z: (k.min[2] + k.max[2]) / 2, hx: (k.max[0] - k.min[0]) / 2, hz: (k.max[2] - k.min[2]) / 2 }))];
  for (const [lx, lz] of [[vd(v).hx + 1, 0], [-vd(v).hx - 1, 0], [0, vd(v).hz + 1], [0, -vd(v).hz - 1]]) {
    const x = v.x + lx * c + lz * s, z = v.z - lx * s + lz * c;
    if (Math.abs(x) <= limX && Math.abs(z) <= limZ && surfaceY(map, x, z, .1) > -.05 && !solid.some(b => Math.abs(x - b.x) < b.hx + BODY.r && Math.abs(z - b.z) < b.hz + BODY.r)) return { x, z };
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
    if (v.driver === shooter || v.gunner === shooter) continue;   // never shoot your own vehicle
    const t = rayVehicle(o, d, v);
    if (t !== null && t < best.t) best = { t, who: null, veh: v };   // the vehicle takes the hit (see applyHit); a wreck still stops bullets
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

function seatFor(v, x, z) {   // which seat of a car a person standing at x, z can take (null if both are taken). With nobody aboard you choose by where you stand: the back of the car is the roof gun, the front and sides are the wheel.
  if (v.driver) return v.gunner ? null : 'g';
  if (v.gunner) return 'd';   // the gun is manned, the wheel is free
  return (x - v.x) * -Math.sin(v.yaw) + (z - v.z) * -Math.cos(v.yaw) < -.6 ? 'g' : 'd';
}
function leaveVehicle(p, notify) {
  const v = vehicles.find(x => x.id === p.vehicle);
  p.vehicle = 0; p.seat = 0;
  if (!v) return;
  if (v.gunner === p) v.gunner = null;   // a roof gunner steps off and the driver carries on
  else { v.driver = null; v.speed = 0; v.y = v.sy || 0; }   // an empty helicopter settles. A roof gunner stays on the gun of the parked car
  if (notify) { const s = exitSpot(v); p.x = s.x; p.z = s.z; p.y = 0; p.sock.emit('undrive', { x: s.x, z: s.z }); }
  emit('vehicles', vehRows());
}

function hurt(shooter, target, dmg, head, how) {
  const dealt = Math.max(0, Math.min(dmg, target.hp));   // points for the yellow popup: what the target really lost, so a 9999 blast on a 40 hp player scores 40
  target.hp -= dmg;
  if (target.bot && shooter && shooter !== target) { target.hitBy = shooter; target.hitAt = Date.now(); }   // a bot that is shot knows which way it came from (a damage marker, not a sound)
  const dead = target.hp <= 0;
  shooter.sock.emit('hit', { kill: dead, head: !!head, dmg: shooter === target ? 0 : Math.round(dealt), how: how || '' });   // dmg feeds the yellow score popups (0 = your own blast, no points)
  if (!dead) { emitYou(target); return; }
  target.hp = 0; target.alive = false; target.deaths++; shooter.kills++; target.respawnAt = Date.now() + RESPAWN_MS; target.reloadEnd = 0;
  if (target.vehicle) leaveVehicle(target, false);
  if (DROPS_ON) dropWeapon(target);   // off by default: the weapon they held is gone with them
  if (match.mode === 'tdm') match.team[shooter.faction]++;
  const awards = killStats(shooter, target, head, how), hs = !!head && !how; stat(target, 'deaths');   // counted before grant(), which sends the shooter their updated profile
  grant(shooter, XP_PER_KILL + (hs ? XP_PER_HEADSHOT : 0), COINS_PER_KILL, 'kill', hs);   // a headshot kill: the kill's XP plus the headshot's
  match.hot = { x: target.x, z: target.z, t: Date.now() };   // where the last fight was, for bots with nothing in sight
  emitYou(target);
  emit('kill', { k: shooter.id, v: target.id, kn: shooter.name, vn: target.name, kf: shooter.faction, vf: target.faction, kl: lvOf(shooter), vl: lvOf(target), hs: !!head, how: how || '', r: RESPAWN_MS, xp: XP_PER_KILL, hx: hs ? XP_PER_HEADSHOT : 0 });
  sendScores();
  if (target !== shooter) saveProfile(target);   // their death is on their profile now
  if (shooter.sock) for (const a of awards) shooter.sock.emit('award', { name: a });   // after the kill, so the popup reads: hit, kill, award
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
  p.streak = 0; p.multi = 0; stat(p, 'deaths'); saveProfile(p);
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
      if (!inBox(s.x, s.y + 1, s.z) || (b.edge === 'wall' && (Math.abs(s.x) > (m.ex || m.half) - R || Math.abs(s.z) > (m.ez || m.half) - R))) bad.push(tag + ' is outside the boundary');
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
const nextMode = () => MODE === 'rotate' ? randOf(['tdm', 'ffa']) : match.mode;   // a random game mode each match too (it can repeat, there is no fixed order)
const nextMapId = () => MAP_ENV !== 'rotate' ? MAP_ENV : randOf(MAP_IDS.filter(id => id !== map.id));   // a random map each time, never the one just played

function endMatch(winner, wf, winners) {
  if (match.state !== 'live') return;
  match.state = 'over';
  const won = new Set(winners || []);
  for (const p of players.values()) {   // everybody who was here for a good part of the match gets a game played; winners get a win and a longer streak
    if (p.bot || !p.token || Date.now() - (p.joinedAt || 0) < 30000) continue;
    stat(p, 'games');
    if (won.has(p)) { stat(p, 'wins'); stat(p, 'winStreak'); statMax(p, 'bestWinStreak', statNum(stOf(p).winStreak)); }
    else if (won.size) statSet(p, 'winStreak', 0);   // somebody else won: the streak is over (a draw leaves it alone)
  }
  for (const p of winners || []) grant(p, 0, WIN_COINS, 'win');
  for (const p of players.values()) if (!won.has(p)) saveProfile(p);   // the winners were just sent theirs by grant()
  for (const p of players.values()) if (!p.bot && p.token && p.sock && (p.mx || Date.now() - (p.joinedAt || 0) >= 30000)) p.sock.emit('report', matchReport(p, won.has(p)));   // the results card slides up on everyone who took part
  const next = nextMode(), nextMap = nextMapId();
  emit('match', { ...matchInfo(), winner, wf, next, nextMap: MAPS[nextMap].name, ms: INTERMISSION_MS });
  { const room = cur; nextTimer = setTimeout(() => inRoom(room, () => startMatch(next, nextMap)), INTERMISSION_MS); }   // the timer fires outside any room, so re-enter this one
}

function timeUp() {   // the clock ran out: the higher team (or the top killer) wins; level scores are a draw
  if (match.mode === 'tdm') {
    const a = match.team.vanguard, b = match.team.horizon;
    if (a === b) endMatch('TIME UP: DRAW', 'ffa', []);
    else { const f = a > b ? 'vanguard' : 'horizon'; endMatch('TIME UP: ' + f.toUpperCase() + ' WINS', f, [...players.values()].filter(p => p.faction === f)); }
  } else {
    const top = [...players.values()].sort((x, y) => y.kills - x.kills)[0];
    if (!top || top.kills === 0) endMatch('TIME UP: DRAW', 'ffa', []); else endMatch('TIME UP: ' + top.name + ' WINS', 'ffa', [top]);
  }
}
function startMatch(mode, mapId) {
  clearTimeout(nextTimer);
  map = MAPS[mapId] || map;
  match.mode = mode; match.state = 'live'; match.team = { vanguard: 0, horizon: 0 }; match.endsAt = Date.now() + MATCH_MS;
  vehicles = vehDefs(map).map((d, i) => ({ id: i + 1, team: d.team || null, sentry: d.sentry || 0, type: d.type || 'car', x: d.x, y: d.y || 0, sy: d.y || 0, z: d.z, yaw: d.yaw, speed: 0, driver: null, gunner: null, dirty: false, heat: 0, lockUntil: 0, hp: (VARM[d.type || 'car'] || { hp: 0 }).hp, dead: false, deadAt: 0, home: { x: d.x, y: d.y || 0, z: d.z, yaw: d.yaw } }));
  for (const p of players.values()) p.vehicle = 0;
  const list = [...players.values()].sort(() => Math.random() - .5), flip = Math.random() < .5 ? 1 : 0;   // random split into teams
  list.forEach((p, i) => { p.kills = p.deaths = 0; p.streak = p.multi = 0; p.mx = null; p.faction = mode === 'tdm' ? ((i + flip) % 2 ? 'horizon' : 'vanguard') : 'ffa'; });
  emit('map', clientMap(map));
  pickups = (map.pickups || []).map((d, i) => ({ id: 'm' + i, wi: d.fixed != null ? d.fixed : randOf(POWER), fixed: d.fixed, x: d.x, y: d.y, z: d.z, up: true, back: 0, drop: false })); emit('pk', pickupRows()); makeTurrets();
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
// Bot levels follow a real player population: most people never get past level 10, and a level 100 is a one-in-ten-thousand sight. [lowest level, highest level, share of all bots]
const LEVEL_BANDS = [[1, 10, .75], [11, 20, .145], [21, 30, .065], [31, 40, .03],               // the shares you gave for levels 1-40 (75%, 14.5%, 6.5%, 3%)
  [41, 50, .005], [51, 60, .0025], [61, 70, .0012], [71, 80, .0007], [81, 90, .00035], [91, 99, .00015], [100, 100, .0001]];   // the last 1% thins out fast: 0.5% reach the 40s, and 1 bot in 10,000 is level 100
function rollBotLevel() {
  let r = Math.random(), band = LEVEL_BANDS[LEVEL_BANDS.length - 1];
  for (const b of LEVEL_BANDS) { if (r < b[2]) { band = b; break; } r -= b[2]; }
  return band[0] + Math.floor((band[1] - band[0] + 1) * Math.pow(Math.random(), 1.5));   // inside a band the lower levels are more common
}
function spawnBot() {
  const id = nextId++, body = randOf(PREMIUM), weapon = randOf(SKINS.filter(s => s.slot === 'weapon')).id, frame = randOf(SKINS.filter(s => s.slot === 'frame')).id;   // every bot: a random premium skin and a random exoskeleton
  const b = {
    id, key: 'bot' + id, bot: true, sock: BOT_SOCK, token: null, prof: { xp: 0, coins: 0, kills: 0, owned: [body, weapon, frame], eq: { body, weapon, frame } },
    lv: rollBotLevel(), shopAt: 0, name: botName(), faction: pickFaction(), x: 0, y: 0, z: 0, yaw: 0, pitch: 0, last: 0, lastVeh: 0, useAt: 0,
    hp: HP, alive: true, kills: 0, deaths: 0, ammos: WEAPONS.map(w => w.magazineSize), reserve: WEAPONS.map(w => w.maxAmmo), held: new Set(), wi: 0, vehicle: 0, reloadEnd: 0, nextShot: 0,
    respawnAt: 0, epoch: 0, rtt: 0, hist: [], nameAt: 0, vy: 0, onGround: true, strafe: 1, strafeAt: 0, stuck: 0, detourUntil: 0, detour: 0, panic: null, goal: null, goalAt: 0
  };
  b.hp = maxHp(b);
  b.loadout = botLoadout(); b.wi = b.loadout[0];   // a bot only starts with a weapon a level 10 player could use
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
// ---- bot navigation: each map is memorised once as a grid of cells a bot (or, when wide, a vehicle) can stand in, and routes across it are found with A* ----
const NAV = new Map(), DI = [1, -1, 0, 0, 1, 1, -1, -1], DJ = [0, 0, 1, -1, 1, -1, 1, -1];
function navFor(m, wide) {
  if (m.ground == null) return null;   // floating deck maps have several levels: bots steer by sight there
  const key = m.id + (wide ? 'w' : ''); if (NAV.has(key)) return NAV.get(key);
  const cs = m.big ? 4 : 2, n = Math.ceil(m.half * 2 / cs), org = -m.half, rad = wide ? 2.8 : BODY.r + .3, edgeX = (m.ex || m.half) - 1.5 - (wide ? 1.5 : 0), edgeZ = (m.ez || m.half) - 1.5 - (wide ? 1.5 : 0), W = new Uint8Array(n * n);
  for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) {
    const x = org + (i + .5) * cs, z = org + (j + .5) * cs; let ok = Math.abs(x) < edgeX && Math.abs(z) < edgeZ;
    if (ok) for (const k of m.blocks) { const y0 = k.y || 0; if (y0 < 1.8 && y0 + k.h > 1.3 && Math.abs(x - k.x) < k.hx + rad && Math.abs(z - k.z) < k.hz + rad) { ok = false; break; } }
    if (ok) for (const k of m.killZones) if (x >= k.min[0] - 1 && x <= k.max[0] + 1 && z >= k.min[2] - 1 && z <= k.max[2] + 1) ok = false;
    W[j * n + i] = ok ? 1 : 0;
  }
  const N = n * n, nav = { n, cs, org, W, g: new Float32Array(N), f: new Float32Array(N), from: new Int32Array(N), mark: new Int32Array(N), done: new Int32Array(N), stamp: 0 };
  NAV.set(key, nav); return nav;
}
function navLine(nav, x0, z0, x1, z1) {   // is the straight line between two points over walkable cells only?
  const steps = Math.ceil(Math.hypot(x1 - x0, z1 - z0) / (nav.cs * .5));
  for (let s = 1; s <= steps; s++) { const t = s / steps, i = Math.floor((x0 + (x1 - x0) * t - nav.org) / nav.cs), j = Math.floor((z0 + (z1 - z0) * t - nav.org) / nav.cs); if (i < 0 || j < 0 || i >= nav.n || j >= nav.n || !nav.W[j * nav.n + i]) return false; }
  return true;
}
function navPath(nav, sx, sz, gx, gz) {   // A* across the grid, then pulled straight wherever the way is clear. Returns [[x, z], ...] or null
  const { n, cs, org, W, g, f, from, mark, done } = nav;
  const near = (x, z) => {
    const i0 = clamp(Math.floor((x - org) / cs), 0, n - 1), j0 = clamp(Math.floor((z - org) / cs), 0, n - 1); if (W[j0 * n + i0]) return j0 * n + i0;
    for (let r = 1; r < 12; r++) for (let dj = -r; dj <= r; dj++) for (let di = -r; di <= r; di++) { if (Math.max(Math.abs(di), Math.abs(dj)) !== r) continue; const i = i0 + di, j = j0 + dj; if (i >= 0 && j >= 0 && i < n && j < n && W[j * n + i]) return j * n + i; }
    return -1;
  };
  const s = near(sx, sz), t = near(gx, gz); if (s < 0 || t < 0) return null;
  const stamp = ++nav.stamp, ti = t % n, tj = (t / n) | 0, open = [];
  const h = i => { const a = Math.abs((i % n) - ti), b = Math.abs(((i / n) | 0) - tj); return a + b - .586 * Math.min(a, b); };
  const push = i => { open.push(i); let a = open.length - 1; while (a > 0) { const b = (a - 1) >> 1; if (f[open[b]] <= f[open[a]]) break; [open[a], open[b]] = [open[b], open[a]]; a = b; } };
  const pop = () => { const top = open[0], last = open.pop(); if (open.length) { open[0] = last; let a = 0; for (;;) { const l = a * 2 + 1, r = l + 1; let m = a; if (l < open.length && f[open[l]] < f[open[m]]) m = l; if (r < open.length && f[open[r]] < f[open[m]]) m = r; if (m === a) break; [open[a], open[m]] = [open[m], open[a]]; a = m; } } return top; };
  mark[s] = stamp; g[s] = 0; from[s] = -1; f[s] = h(s); push(s);
  let found = false, iter = 0;
  while (open.length && iter++ < 30000) {
    const c = pop(); if (c === t) { found = true; break; } if (done[c] === stamp) continue; done[c] = stamp;
    const ci = c % n, cj = (c / n) | 0;
    for (let k = 0; k < 8; k++) {
      const di = DI[k], dj = DJ[k], i = ci + di, j = cj + dj; if (i < 0 || j < 0 || i >= n || j >= n) continue;
      const q = j * n + i; if (!W[q] || (di && dj && (!W[cj * n + i] || !W[j * n + ci]))) continue;   // no cutting corners
      const ng = g[c] + (di && dj ? 1.414 : 1); if (mark[q] === stamp && ng >= g[q]) continue;
      mark[q] = stamp; g[q] = ng; from[q] = c; f[q] = ng + h(q); push(q);
    }
  }
  if (!found) return null;
  const pts = []; for (let c = t; c >= 0; c = from[c]) pts.push([org + ((c % n) + .5) * cs, org + (((c / n) | 0) + .5) * cs]); pts.reverse();
  const out = []; let a = [sx, sz], idx = 0;
  while (idx < pts.length) { let far = idx; for (let k = pts.length - 1; k > idx; k--) if (navLine(nav, a[0], a[1], pts[k][0], pts[k][1])) { far = k; break; } out.push(pts[far]); a = pts[far]; idx = far + 1; }
  return out;
}
function routeStep(st, nav, x, z, gx, gz, now) {   // the next point to walk to: straight at the goal when the line is clear, otherwise along a remembered A* route
  if (!nav || navLine(nav, x, z, gx, gz)) { st.path = null; return [gx, gz]; }
  if (!st.path || now > st.at || Math.hypot(gx - st.gx, gz - st.gz) > 6) { st.path = navPath(nav, x, z, gx, gz); st.at = now + (map.big ? 1600 : 1000); st.gx = gx; st.gz = gz; st.i = 0; }
  if (!st.path || !st.path.length) return [gx, gz];
  while (st.i < st.path.length - 1 && Math.hypot(st.path[st.i][0] - x, st.path[st.i][1] - z) < nav.cs * .9) st.i++;
  return st.path[st.i];
}
// ---- bots and rides: a free vehicle or pillar gun, or the roof gun of a friendly car that already has a driver ----
const botCanUse = (p, v) => v.dead ? false : v.type === 'turret' ? !v.driver && (!v.team || match.mode !== 'tdm' || v.team === p.faction) : v.type === 'car' ? (!v.driver || !v.gunner) && (match.mode !== 'tdm' || !v.driver || v.driver.faction === p.faction) && (match.mode !== 'tdm' || !v.gunner || v.gunner.faction === p.faction) : !v.driver;
function botPickVehicle(p) {
  let best = null, bd = 90;
  for (const v of vehicles) { if (!botCanUse(p, v)) continue; const d = Math.hypot(v.x - p.x, v.z - p.z) * (v.type === 'turret' ? .8 : 1); if (d < bd) { bd = d; best = v; } }
  return best;
}
function boardBot(p, v, now) {
  const gun = !!v.driver; if (gun) { v.gunner = p; p.seat = 'g'; } else v.driver = p;
  p.vehicle = v.id; p.reloadEnd = 0; p.drove = now; p.stuck = 0; p.goalVeh = 0; p.lastSeen = now; p.gunTgt = null; p.rt1 = {}; p.rt2 = {};
  if (v.type === 'turret') { p.x = v.x; p.z = v.z; p.y = v.sy; } else if (!gun) { v.speed = 0; v.dirty = true; }
  emit('vehicles', vehRows());
}
// What a bot can see. Only sight counts, never hearing: an enemy has to be inside the bot's view range, inside the cone the bot is facing, and not hidden behind a wall.
// Behind and to the sides is blind. Better bots see further and a little wider. A target already being tracked is kept while it stays in view, even if the bot is still turning to face it.
function botSees(p, q, eye, facing, skill, tracked) {
  const dx = q.x - eye.x, dy = q.y + 1.2 - eye.y, dz = q.z - eye.z, d = Math.hypot(dx, dy, dz) || 1;
  if (d > 60 + 90 * skill) return false;
  if (Math.abs(wrap(Math.atan2(-dx, -dz) - facing)) > (tracked ? 1.9 : .9 + .45 * skill)) return false;
  const look = cast(p, eye, { x: dx / d, y: dy / d, z: dz / d }, d);
  return look.who === q || look.t >= d - 1 || (look.veh && look.veh.id === q.vehicle);
}
const roamGoal = () => match.hot && Date.now() - match.hot.t < 25000 && Math.random() < .45 ? { x: match.hot.x + (Math.random() - .5) * 30, z: match.hot.z + (Math.random() - .5) * 30 } : Math.random() < .3 ? { x: (map.centre || [0, 0])[0], z: (map.centre || [0, 0])[1] } : randOf(map.spawns.ffa);   // with nothing in sight: head for where a fight was just seen in the kill feed, the middle, or a spawn area
function botGun(p, v, now) {   // on a pillar gun or a car's roof gun: swing at the nearest enemy it can see and fire in bursts
  const w = VWEAPONS[p.seat ? 'cargun' : 'turret'], o = { x: v.x, y: (v.y || 0) + (p.seat ? 2.4 : 1.3), z: v.z }, skill = p.skill ?? (p.skill = botSkill(p.lv));
  let tgt = null, best = w.range;
  for (const q of players.values()) {
    if (q === p || !q.alive || q.vehicle === p.vehicle || (match.mode === 'tdm' && q.faction === p.faction)) continue;
    const d = Math.hypot(q.x - o.x, q.y + 1.2 - o.y, q.z - o.z); if (d >= best) continue;
    if (botSees(p, q, o, p.yaw, skill, q === p.gunTgt)) { best = d; tgt = q; }   // only targets in the gun's field of view with a clear line
  }
  if (tgt) p.lastSeen = now;
  if (now - (p.lastSeen || p.drove) > 9000 || now - p.drove > 70000) { leaveVehicle(p, true); p.boardAt = now + 8000; p.seekAt = now + 15000; return; }
  if (!p.seat) { p.x = v.x; p.z = v.z; p.y = v.sy; }
  if (!tgt) { p.yaw = r3(wrap(p.yaw + .03)); if (!p.seat) { v.yaw = p.yaw; v.dirty = true; } return; }   // nothing in view: the gun slowly sweeps round looking
  const dx = tgt.x - o.x, dy = tgt.y + 1.2 - o.y, dz = tgt.z - o.z, want = Math.atan2(-dx, -dz); p.yaw = r3(want); p.pitch = r3(clamp(Math.atan2(dy, Math.hypot(dx, dz)), -1.2, 1.2));
  if (!p.seat) { v.yaw = r3(wrap(v.yaw + clamp(wrap(want - v.yaw), -.12 - skill * .08, .12 + skill * .08))); v.dirty = true; if (Math.abs(wrap(want - v.yaw)) > .15) return; }
  if (p.gunTgt !== tgt) { p.gunTgt = tgt; p.nextShot = Math.max(p.nextShot, now + 500 - 350 * skill + Math.random() * 300); }   // a moment to react to a new target
  if (now < p.nextShot) return;
  const e = (.03 + best * .0014) * (1.9 - 1.5 * skill), d = { x: dx / best + (Math.random() - .5) * 2 * e, y: dy / best + (Math.random() - .5) * 2 * e, z: dz / best + (Math.random() - .5) * 2 * e }, l = Math.hypot(d.x, d.y, d.z);
  d.x /= l; d.y /= l; d.z /= l; p.nextShot = now + w.fireRateDelay + Math.random() * 60;
  const hit = cast(p, o, d, w.range), t = hit.t;
  emit('fx', { a: [r2(o.x), r2(o.y), r2(o.z)], b: [r2(o.x + d.x * t), r2(o.y + d.y * t), r2(o.z + d.z * t)], f: p.faction, s: p.prof.eq.weapon, i: p.id, e: 0 });
  applyHit(p, hit, o, d, w);
}
const botSkill = lv => {   // 0 hopeless .. 1 perfect. Skill climbs quickly over the first levels and slowly after: level 5 is poor (about .15), 20 is .33, 40 is .51, 70 is .74, and only level 100 is close to perfect (.95).
  const base = .06 + .89 * Math.pow(Math.min(lv, 100) / 100, .75), jitter = (Math.random() - .5) * .14;   // equal levels still differ a little
  return clamp(base + jitter, .05, Math.min(.97, base + .07));   // nobody plays above their level
};
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
    if (now > (p.boardAt || 0)) {   // a usable ride within reach: press E (always for the one it is heading for)
      p.boardAt = now + 500;
      const v = vehicles.find(x => botCanUse(p, x) && (x.id === p.goalVeh || (!p.goalVeh && Math.random() < .5)) && distToVehicle(x, p.x, p.z) < 1.7 && (x.type === 'turret' || Math.abs((x.y || 0) - p.y) < 3));
      if (v) { boardBot(p, v, now); continue; }
    }
    const skill = p.skill ?? (p.skill = botSkill(p.lv)), turnR = BOT.turn * (.4 + .7 * skill);
    if (now > (p.percAt || 0)) {   // a bot looks about five times a second, and only notices what it can actually see: in range, in front of it, with nothing in the way
      p.percAt = now + 160 + Math.random() * 100; const eye = { x: p.x, y: p.y + BODY.eye, z: p.z }; let seen = null, sd = Infinity;
      for (const q of players.values()) { if (q === p || !q.alive || (match.mode === 'tdm' && q.faction === p.faction)) continue; const d = Math.hypot(q.x - p.x, q.y - p.y, q.z - p.z); if (d < sd && botSees(p, q, eye, p.yaw, skill, q === p.vis)) { sd = d; seen = q; } }
      p.vis = seen; if (seen) p.mem = { x: seen.x, z: seen.z, until: now + 2500 + 3500 * skill };   // it remembers where it last saw someone for a few seconds
      if (!seen && p.hitBy && p.hitBy.alive && p.hitDone !== p.hitAt && now - p.hitAt < 800) { p.hitDone = p.hitAt; p.mem = { x: p.hitBy.x, z: p.hitBy.z, until: now + 3500 }; }   // shot from out of sight: it turns toward where the hit came from, like a damage marker
    }
    let tgt = p.vis && p.vis.alive ? p.vis : null, best = tgt ? Math.hypot(tgt.x - p.x, tgt.y - p.y, tgt.z - p.z) : Infinity;
    if (!tgt && p.mem && now < p.mem.until) { p.goal = { x: p.mem.x, z: p.mem.z }; p.goalAt = now + 600; if (Math.hypot(p.mem.x - p.x, p.mem.z - p.z) < 3) p.mem = null; }   // go and look where it last saw someone
    if (tgt !== p.lastTgt) { p.lastTgt = tgt; p.reactAt = now + (900 - 700 * skill) + Math.random() * 400; }   // a new target takes a moment to notice: slower for weaker bots
    if (tgt && now > (p.wsAt || 0) && !p.reloadEnd) { p.wsAt = now + 1200; const ok = i => p.ammos[i] > 0 || p.reserve[i] > 0; let pick = p.wi, bs = -1e9; for (const i of new Set([...p.loadout, ...p.held])) { if (!ok(i)) continue; const w1 = WEAPONS[i], sc = -Math.abs(best - w1.range * .4) - (w1.splash && best < 8 ? 60 : 0); if (sc > bs) { bs = sc; pick = i; } } if (pick !== p.wi) p.wi = pick; }   // each weapon has a distance it likes   // sniper at range, rockets mid range, rifle up close
    if (!p.goalVeh && now > (p.seekAt || 0)) { p.seekAt = now + 4000; if ((!tgt || best > 30) && Math.random() < .2 + skill * .4) { const v = botPickVehicle(p); if (v) { p.goalVeh = v.id; p.goalVehAt = now + 30000; } } }   // fancy a ride or a gun?
    if (!tgt && (!p.goal || now > p.goalAt || Math.hypot(p.goal.x - p.x, p.goal.z - p.z) < 3)) { p.goal = roamGoal(); p.goalAt = now + 8000; }
    const gv = p.goalVeh ? vehicles.find(v => v.id === p.goalVeh && botCanUse(p, v)) : null; if (p.goalVeh && (!gv || now > p.goalVehAt)) p.goalVeh = 0;
    const toVeh = !!gv && (!tgt || best > 22), hold = !!tgt && !toVeh;   // heading for a ride, or hunting
    const gx = toVeh ? gv.x : tgt ? tgt.x : p.goal.x, gy = hold ? tgt.y + 1.2 + .38 * clamp((skill - .75) / .2, 0, 1) : p.y + BODY.eye, gz = toVeh ? gv.z : tgt ? tgt.z : p.goal.z;
    const rt = p.rt1 || (p.rt1 = {}), nearV = toVeh && Math.hypot(gx - p.x, gz - p.z) < 7, [rx, rz] = nearV ? [gx, gz] : routeStep(rt, navFor(map, false), p.x, p.z, gx, gz, now), rl0 = Math.hypot(rx - p.x, rz - p.z) || 1;   // the memorised route's next point
    if (nearV) rt.path = null;
    const faceT = hold && !rt.path;   // face the target when the way is clear, the route when it bends
    const dx = gx - p.x, dy = gy - (p.y + BODY.eye), dz = gz - p.z, flat = Math.hypot(dx, dz) || 1, dist = Math.hypot(dx, dy, dz) || 1;   // the 3D vector to the target
    const wantYaw = faceT ? Math.atan2(-dx, -dz) : Math.atan2(-(rx - p.x), -(rz - p.z));
    p.yaw = r3(wrap(p.yaw + clamp(wrap(wantYaw - p.yaw), -turnR, turnR)));                                      // turn smoothly, never snap
    p.pitch = r3(clamp(p.pitch + clamp(Math.atan2(dy, flat) - p.pitch, -.12, .12), -1.2, 1.2));
    if (p.hp >= maxHp(p) * .3) p.panic = null; else if (p.panic === null) p.panic = Math.random() < .4 ? (Math.random() < .5 ? 'strafe' : 'jump') : 'none';   // below 30% health: 40% panic
    if (now > p.strafeAt) { p.strafe = -p.strafe; p.strafeAt = now + 500 + skill * 500 + Math.random() * 700; }
    const w0 = W(p), pref = w0.short === 'SNIPER' ? 55 : w0.short === 'ROCKET' ? 28 : 13, hurtBad = p.hp < maxHp(p) * .3 && skill > .35;   // each weapon wants a fighting distance
    const fx = (rx - p.x) / rl0, fz = (rz - p.z) / rl0, side = rt.path ? 0 : p.panic === 'strafe' || (hold && flat < pref * 1.7) ? p.strafe : 0;
    const fwd = !hold ? 1 : hurtBad ? -.7 : flat < 3 ? 0 : flat > pref ? 1 : skill > .5 && flat < pref * .5 ? -.5 : .2;   // close in, hold at range, back off if hurt or if good enough to know better
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
    if (!hold || !faceT || p.reloadEnd || now < p.nextShot || now < (p.reactAt || 0) || Math.abs(wrap(wantYaw - p.yaw)) > .3) continue;
    const w = W(p), o = { x: p.x, y: p.y + BODY.eye, z: p.z }, u = { x: dx / dist, y: dy / dist, z: dz / dist };
    if (dist > w.range) continue;
    if (p.ammos[p.wi] <= 0) { if (p.reserve[p.wi] <= 0 && p.wi) p.wi = 0; else startReload(p); continue; }   // out of rockets or sniper rounds: back to the rifle
    const look = cast(p, o, u, dist); if (look.who !== tgt && look.t < dist - 1 && !(look.veh && look.veh.id === tgt.vehicle)) continue;   // a wall is in the way: keep running, don't waste bullets
    if (Math.random() < (1 - skill) * .25) { p.nextShot = now + 120 + Math.random() * 300; continue; }   // weaker bots hesitate and waste time
    const e = (.025 + dist * .0012) * (.12 + 1.9 * Math.pow(1 - skill, 1.3)) * (p.panic ? 1.6 : 1), d = { x: u.x + (Math.random() - .5) * 2 * e, y: u.y + (Math.random() - .5) * 2 * e, z: u.z + (Math.random() - .5) * 2 * e };
    const l = Math.hypot(d.x, d.y, d.z); d.x /= l; d.y /= l; d.z /= l;                        // the random offset: bots do not have perfect aim
    p.nextShot = now + w.fireRateDelay + Math.random() * 90; p.ammos[p.wi] = Math.max(0, p.ammos[p.wi] - (w.ammoPerShot || 1));
    for (let k = 0; k < (w.pellets || 1); k++) {
      const dd = w.spread ? spreadDir(d, w.spread) : d, t = rayShot(p, o, dd, w);
      if (k < 6) emit('fx', { a: [r2(p.x + dd.x * .7), r2(o.y + dd.y * .7), r2(p.z + dd.z * .7)], b: [r2(o.x + dd.x * t), r2(o.y + dd.y * t), r2(o.z + dd.z * t)], f: p.faction, s: p.prof.eq.weapon, i: p.id, e: w.splash ? w.splash.radius : 0 });
    }
    if (p.alive && p.ammos[p.wi] <= 0) startReload(p);
  }
}

// ---- weapons in the world: a few map pickups, hidden away. Once somebody takes one it is gone for everyone until the 5 minute cooldown ends, and then it comes back as a new weapon.
// The dead no longer drop what they were holding (set DROPS=on to bring that back), so a good weapon can never be passed on.
// E swaps what you hold for the pickup within reach. Everyone respawns with the assault rifle. ----
const PICKUP_RESPAWN_MS = (Number(process.env.PICKUP_RESPAWN_MIN) || 5) * 60000, DROP_LIFE_MS = 30000, PICKUP_RANGE = 2.5, MAX_DROPS = 24, DROPS_ON = process.env.DROPS === 'on';
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
  for (let i = pickups.length - 1; i >= 0; i--) { const k = pickups[i]; if (k.drop && now >= k.exp) { pickups.splice(i, 1); changed = true; } else if (!k.up && now >= k.back) { k.up = true; k.wi = k.fixed != null ? k.fixed : randOf(POWER); changed = true; } }
  if (changed) emit('pk', pickupRows());
}
// One shot's damage: a headshot multiplies it, and a rocket also hurts every enemy near the blast (less the further they are; never you or your team).
function destroyVehicle(v, by) {   // a vehicle at zero hit points blows up: everyone inside dies, people close by are hurt, and it is a wreck until it respawns
  if (by && by.token) { stat(by, 'vehKills'); saveProfile(by); }
  v.hp = 0; v.dead = true; v.deadAt = Date.now(); v.speed = 0; v.y = v.sy || 0; v.dirty = true;
  const riders = [v.driver, v.gunner].filter(Boolean); v.driver = null; v.gunner = null;
  for (const p of riders) { p.vehicle = 0; p.seat = 0; p.x = v.x; p.z = v.z; p.y = v.y; if (p.sock) p.sock.emit('undrive', { x: v.x, z: v.z }); if (p.alive) hurt(by || p, p, 9999, false, 'vehicle'); }
  for (const q of [...players.values()]) {
    if (!q.alive || riders.includes(q) || q.vehicle || (by && match.mode === 'tdm' && q.faction === by.faction)) continue;
    const dd = Math.hypot(q.x - v.x, q.z - v.z); if (dd < 7) hurt(by || q, q, Math.round(70 * (1 - dd / 7)), false);
  }
  emit('vexp', { id: v.id, x: r2(v.x), y: r2((v.y || 0) + 1), z: r2(v.z) }); emit('vehicles', vehRows());
}
function damageVehicle(v, dmg, by) {   // returns true if this is the shot that destroyed it
  if (v.dead || !VARM[v.type] || !(dmg > 0)) return false;
  v.hp -= dmg; v.dirty = true;
  if (v.hp <= 0) { destroyVehicle(v, by); return true; }
  return false;
}
function applyHit(shooter, hit, o, dir, w, dist) {
  if (hit.veh) {   // armour: the vehicle soaks the shot, scaled by how heavy the weapon is. A mech's upper back is the exception.
    const v = hit.veh, A = VARM[v.type], friendly = match.mode === 'tdm' && ((v.driver && v.driver.faction === shooter.faction) || (v.gunner && v.gunner.faction === shooter.faction));
    if (A && !v.dead && !friendly) {
      const base = w.damage * (w.falloff && dist != null ? falloffMul(w, dist) : 1);
      let weak = false;
      if (v.type === 'mech') { const hx = o.x + dir.x * hit.t - v.x, hy = o.y + dir.y * hit.t - (v.y || 0), hz = o.z + dir.z * hit.t - v.z, L = Math.hypot(hx, hz) || 1; weak = (hx * -Math.sin(v.yaw) + hz * -Math.cos(v.yaw)) / L < -.5 && hy > 2 && hy < 4.8; }   // behind it, and high up
      const vdmg = weak ? base * A.weak : base * A[weightOf(w)], dealt = Math.round(Math.max(0, Math.min(vdmg, v.hp)));   // what the armour really loses
      const killed = damageVehicle(v, vdmg, shooter);
      if (shooter.sock) shooter.sock.emit('hit', { kill: killed, head: weak, veh: 1, dmg: dealt });   // a gold marker means you found the weak spot
    }
  } else if (hit.who) {
    const dmg = Math.round(w.damage * (w.falloff && dist != null ? falloffMul(w, dist) : 1) * (hit.head ? w.headshotMultiplier : 1) * (w.splash ? 1 - frameOf(hit.who).blast : 1));
    hurt(shooter, hit.who, dmg, hit.head);
    if (w.lifesteal && shooter.alive) { shooter.hp = Math.min(maxHp(shooter), shooter.hp + dmg * w.lifesteal); emitYou(shooter); }   // vampire weapons heal you
    if (w.burn && hit.who.alive) { hit.who.burnUntil = Date.now() + w.burn.secs * 1000; hit.who.burnDps = w.burn.dps; hit.who.burnBy = shooter; }   // and fire keeps burning
  }
  if (!w.splash) return;
  const x = o.x + dir.x * hit.t, y = o.y + dir.y * hit.t, z = o.z + dir.z * hit.t;
  for (const q of [...players.values()]) {
    if (q === shooter || q === hit.who || !q.alive || q.vehicle || (match.mode === 'tdm' && q.faction === shooter.faction)) continue;   // people inside a vehicle are shielded by it
    const d = Math.hypot(q.x - x, q.y + 1 - y, q.z - z);
    if (d < w.splash.radius) { hurt(shooter, q, Math.round(w.splash.damage * (1 - .7 * d / w.splash.radius) * (1 - frameOf(q).blast)), false); if (w.burn && q.alive) { q.burnUntil = Date.now() + w.burn.secs * 1000; q.burnDps = w.burn.dps; q.burnBy = shooter; } }
  }
  for (const v of vehicles) {   // and the blast wears down any vehicle it reaches, at heavy-weapon strength
    const A = VARM[v.type]; if (!A || v.dead || v === hit.veh || v.driver === shooter || v.gunner === shooter) continue;
    if (match.mode === 'tdm' && ((v.driver && v.driver.faction === shooter.faction) || (v.gunner && v.gunner.faction === shooter.faction))) continue;
    const T = vd(v), dv = Math.hypot(v.x - x, (v.y || 0) + T.h / 2 - y, v.z - z) - T.hz; if (dv < w.splash.radius) damageVehicle(v, w.splash.damage * (1 - .7 * Math.max(0, dv) / w.splash.radius) * A.heavy, shooter);
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
    if (v.dead) { if (now - v.deadAt > VEH_RESPAWN_MS) { Object.assign(v, { x: v.home.x, y: v.home.y, z: v.home.z, yaw: v.home.yaw, hp: VARM[v.type].hp, dead: false, speed: 0, dirty: true }); emit('vehicles', vehRows()); } continue; }
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
    const mv = vehicles.find(v => v.sentry === t.id);
    if (mv && mv.driver) { const D = mv.driver; t.yaw = r3(wrap(D.bot ? D.yaw : mv.yaw)); t.pitch = r3(clamp(D.pitch || 0, -1.3, 1.2)); continue; }   // someone is sitting in it: it points where they point and only fires when they do
    let tgt = null, best = TURRET.radius;
    for (const q of players.values()) { if (!q.alive || q.faction === t.faction) continue; const d = Math.hypot(q.x - t.x, q.y + 1 - t.y, q.z - t.z); if (d < best) { best = d; tgt = q; } }
    if (!tgt) continue;
    const dx = tgt.x - t.x, dy = tgt.y + 1.2 - (t.y + TURRET.head), dz = tgt.z - t.z, flat = Math.hypot(dx, dz) || 1, dist = Math.hypot(dx, dy, dz) || 1, want = Math.atan2(-dx, -dz);
    t.yaw = r3(wrap(t.yaw + clamp(wrap(want - t.yaw), -.22, .22))); t.pitch = r3(clamp(t.pitch + clamp(Math.atan2(dy, flat) - t.pitch, -.15, .15), -1.3, 1.2));   // up on its tower it has to look steeply down at anyone near the foot
    if (now < t.nextShot || Math.abs(wrap(want - t.yaw)) > .12) continue;
    const o = { x: t.x + dx / flat * TURRET.reach, y: t.y + TURRET.head, z: t.z + dz / flat * TURRET.reach };   // the muzzle sticks out past the tower's edge, so the gun can fire straight down at anyone standing at its foot
    const ox = tgt.x - o.x, oy = tgt.y + 1.2 - o.y, oz = tgt.z - o.z, od = Math.hypot(ox, oy, oz) || 1, u = { x: ox / od, y: oy / od, z: oz / od };
    const look = cast(t.sh, o, u, od); if (look.who !== tgt && look.t < od - 1 && !(look.veh && look.veh.id === tgt.vehicle)) continue;   // a wall in the way
    const e = .02 + od * .00053, d = { x: u.x + (Math.random() - .5) * 2 * e, y: u.y + (Math.random() - .5) * 2 * e, z: u.z + (Math.random() - .5) * 2 * e }, l = Math.hypot(d.x, d.y, d.z);
    d.x /= l; d.y /= l; d.z /= l; t.nextShot = now + TURRET.fireRateDelay;
    const hit = cast(t.sh, o, d, TURRET.range), tt = hit.t;
    emit('fx', { a: [r2(o.x + d.x * .8), r2(o.y + d.y * .8), r2(o.z + d.z * .8)], b: [r2(o.x + d.x * tt), r2(o.y + d.y * tt), r2(o.z + d.z * tt)], f: t.faction, s: 'w-issue', i: 0, e: 0 });
    applyHit(t.sh, hit, o, d, TURRET);
  }
}
function vehBlocked(v, x, z) {   // a ground vehicle or mech cannot drive through walls or off the map
  const r = vd(v).hx + .4;
  if (Math.abs(x) > (map.ex || map.half) - 3 || Math.abs(z) > (map.ez || map.half) - 3) return true;
  for (const k of map.blocks) if ((k.y || 0) < 2 && (k.y || 0) + k.h > .3 && Math.abs(x - k.x) < k.hx + r && Math.abs(z - k.z) < k.hz + r) return true;
  return false;
}
// A bot at the wheel: cars charge the nearest enemy (the roadkill check does the rest), helicopters climb to 22 m and rocket from range, mechs walk up and use their miniguns.
function botDrive(p, now, dt) {
  const v = vehicles.find(x => x.id === p.vehicle); if (!v) { p.vehicle = 0; return; }
  if (v.type === 'turret' || p.seat) { botGun(p, v, now); return; }
  const skill = p.skill ?? (p.skill = botSkill(p.lv));
  if (now > (p.percAt || 0)) {   // looking out of the windscreen: the same range, view cone and line of sight as on foot, along the way the vehicle faces
    p.percAt = now + 160 + Math.random() * 100; const eye = { x: v.x, y: (v.y || 0) + 1.6, z: v.z }; let seen = null, sd = Infinity;
    for (const q of players.values()) { if (q === p || !q.alive || q.vehicle === p.vehicle || (match.mode === 'tdm' && q.faction === p.faction)) continue; const d = Math.hypot(q.x - v.x, q.z - v.z); if (d < sd && botSees(p, q, eye, v.yaw, skill, q === p.vis)) { sd = d; seen = q; } }
    p.vis = seen; if (seen) { p.lastSeen = now; p.mem = { x: seen.x, z: seen.z, until: now + 3000 + 3000 * skill }; }
  }
  const tgt = p.vis && p.vis.alive ? p.vis : null;
  if (now - (p.lastSeen || p.drove) > 14000 || now - p.drove > 60000 || p.stuck > 40) { leaveVehicle(p, true); p.stuck = 0; p.boardAt = now + 8000; p.seekAt = now + 15000; return; }   // nothing seen for a while, or stuck: get out
  if (!p.vgoal || now > p.vgoalAt) { p.vgoal = roamGoal(); p.vgoalAt = now + 9000; }
  const aim = tgt || (p.mem && now < p.mem.until ? p.mem : p.vgoal);   // what it can see, else where it last saw someone, else a place to look
  const dx = aim.x - v.x, dz = aim.z - v.z, flat = Math.hypot(dx, dz) || 1, want = Math.atan2(-dx, -dz), T = vd(v), w = VWEAPONS[v.type];
  if (!tgt && flat < 12) p.vgoalAt = 0;
  const [rx, rz] = v.type === 'heli' ? [aim.x, aim.z] : routeStep(p.rt2 || (p.rt2 = {}), navFor(map, true), v.x, v.z, aim.x, aim.z, now), mvWant = Math.atan2(-(rx - v.x), -(rz - v.z));   // ground vehicles follow the memorised route
  v.yaw = r3(wrap(v.yaw + clamp(wrap(mvWant - v.yaw), -.08, .08)));
  const sp = (v.type === 'car' ? 18 : v.type === 'tank' ? (flat < 30 ? 0 : 7.5) : v.type === 'heli' ? (flat < 70 ? 0 : 14) : (flat < 40 ? 0 : 4.2)) * (v.type === 'heli' ? 1 : clamp(1.15 - Math.abs(wrap(mvWant - v.yaw)), .2, 1));   // slow down to turn corners
  const nx = v.x - Math.sin(v.yaw) * sp * dt, nz = v.z - Math.cos(v.yaw) * sp * dt;
  if (v.type === 'heli' || !vehBlocked(v, nx, nz)) { v.x = nx; v.z = nz; p.stuck = 0; } else { v.yaw = r3(wrap(v.yaw + .5)); p.stuck++; }   // blocked: swing away
  if (v.type === 'heli') v.y = Math.min(22, (v.y || 0) + 6 * dt);
  const limX = (map.ex || map.half) - T.hx, limZ = (map.ez || map.half) - T.hx; v.x = r2(clamp(v.x, -limX, limX)); v.z = r2(clamp(v.z, -limZ, limZ)); v.speed = sp; v.dirty = true;
  p.x = v.x; p.y = v.y || 0; p.z = v.z; p.yaw = v.yaw;
  if (!tgt || !w || flat > w.range * .9 || Math.abs(wrap(want - v.yaw)) > .25 || now < p.nextShot || (v.type === 'heli' && v.y < 15)) return;
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
// ---- The server list: MAX_ROOMS servers (50 by default) named Server-US-1 .. Server-US-50. Each is a real room that opens the first time somebody joins it, with the map and mode the list showed.
// The player counts on the list are display numbers between 10 and 15 out of 16 that drift now and then, so every server looks open to join (every room fills itself to 16 with bots anyway).
const slotName = n => 'Server-' + REGION + '-' + n;
const slotNo = id => { const m = typeof id === 'string' && /^Server-[A-Z]+-(\d{1,3})$/.exec(id), n = m ? Number(m[1]) : 0; return n >= 1 && n <= MAX_ROOMS && id === slotName(n) ? n : 0; };
const plans = new Map(), crowd = new Map();   // what an unopened server will play, and the numbers shown for each server
const planOf = id => { let p = plans.get(id); if (!p) { p = { mode: MODE === 'rotate' ? randOf(['tdm', 'ffa']) : MODE, map: MAP_ENV === 'rotate' ? randOf(MAP_IDS) : MAP_ENV }; plans.set(id, p); } return p; };
const shownPlayers = (id, now) => { let c = crowd.get(id); if (!c) { c = { n: 10 + Math.floor(Math.random() * 6), t: now + 15000 + Math.random() * 25000 }; crowd.set(id, c); } if (now > c.t) { c.n = clamp(c.n + (Math.random() < .5 ? -1 : 1), 10, 15); c.t = now + 15000 + Math.random() * 25000; } return c.n; };
function serverList() {
  const now = Date.now();
  return { max: MAX_PLAYERS, servers: Array.from({ length: MAX_ROOMS }, (_, i) => { const id = slotName(i + 1), r = rooms.get(id), pl = r ? { mode: r.match.mode, map: r.map.id } : planOf(id); return { id, n: i + 1, region: REGION, map: MAPS[pl.map].name, mode: pl.mode, players: shownPlayers(id, now), max: MAX_PLAYERS }; }) };
}
app.get('/servers', (req, res) => { res.set('Access-Control-Allow-Origin', '*'); res.set('Cache-Control', 'no-store'); res.json(serverList()); });
function createRoom(wanted) {
  let n = slotNo(wanted); if (!n) for (n = 1; n <= MAX_ROOMS && rooms.has(slotName(n)); n++);   // the server asked for, else the first one not open yet
  const room = { id: slotName(n), players: new Map(), match: { mode: 'tdm', state: 'live', team: { vanguard: 0, horizon: 0 } }, map: MAPS.field, vehicles: [], tick: 0, nextTimer: null, spawnHeld: new Map(), pickups: [], turrets: [], emptySince: 0 };
  rooms.set(room.id, room);
  const plan = planOf(room.id); plans.delete(room.id);   // it opens with the map and mode the list showed; every match after that picks a random map and mode
  inRoom(room, () => startMatch(plan.mode, plan.map));
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
  const auth = (socket.handshake && socket.handshake.auth) || {}, want = slotNo(auth.server);   // the server picked from the list, if it is a real one
  let room = want ? rooms.get(auth.server) || (rooms.size < MAX_ROOMS ? createRoom(auth.server) : null) : null;
  if (room && humansIn(room) >= MAX_PLAYERS) room = null;   // it is full of people: play wherever there is space
  room = room || matchmake();
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
    hp: HP, alive: true, kills: 0, deaths: 0, ammos: WEAPONS.map(w => w.magazineSize), reserve: WEAPONS.map(w => w.maxAmmo), held: new Set(), wi: 0, vehicle: 0, reloadEnd: 0, nextShot: 0, respawnAt: 0, epoch: 0, rtt: 100, hist: [], nameAt: 0, joinedAt: Date.now()
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
    else { if (me.ammos[me.wi] <= 0) { startReload(me); return; } me.nextShot = now + w.fireRateDelay * .8; me.ammos[me.wi] = Math.max(0, me.ammos[me.wi] - (w.ammoPerShot || 1)); }
    for (let k = 0; k < (w.pellets || 1); k++) {   // shotguns and burst rifles send several rays per trigger pull
      const dd = w.spread ? spreadDir(dir, w.spread) : dir, t = rayShot(me, o, dd, w);
      if (k < 6) socket.to(room.id).emit('fx', {                                                    // let everyone else see the tracer
        a: veh ? [r2(o.x), r2(o.y), r2(o.z)] : [r2(me.x + dd.x * .7), r2(me.y + BODY.eye + dd.y * .7), r2(me.z + dd.z * .7)],
        b: [r2(o.x + dd.x * t), r2(o.y + dd.y * t), r2(o.z + dd.z * t)], f: me.faction, s: profOf(me).eq.weapon, i: me.id, e: w.splash ? w.splash.radius : 0
      });
    }
    if (!veh && me.alive && me.ammos[me.wi] <= 0) startReload(me);
  });

  on('reload', () => { if (me.alive && !me.vehicle && match.state === 'live') startReload(me); });

  on('switch', i => {                      // changing weapon cancels a reload and costs a short draw time
    if (!Number.isInteger(i) || i < 0 || i >= WEAPONS.length || i === me.wi || !me.alive || me.vehicle) return;
    if (!me.held.has(i) && !(me.loadout || []).includes(i)) { emitYou(me); return notice(me, WEAPONS[i].name + ' is not in your loadout: set it in the shop, or find one on the map'); }
    me.wi = i; me.reloadEnd = 0; me.nextShot = Math.max(me.nextShot, Date.now() + SWITCH_MS);
    emitYou(me);
  });

  on('use', () => {                        // the E key
    const now = Date.now();
    if (!me.alive || match.state !== 'live' || now - me.useAt < 250) return;
    me.useAt = now;
    if (me.vehicle) { leaveVehicle(me, true); return; }
    if (takePickup(me, now)) return;   // a weapon within reach comes before a vehicle
    let best = null, bd = 99, gun = false;
    for (const v of vehicles) {   // the wheel of a free vehicle, a pillar gun, or either seat of a car (the roof gun can be manned with nobody driving)
      if (v.dead) continue;
      const seat = v.type === 'car' ? seatFor(v, me.x, me.z) : v.driver ? null : 'd'; if (!seat) continue;
      if (match.mode === 'tdm' && v.type === 'car' && ((seat === 'g' && v.driver && v.driver.faction !== me.faction) || (seat === 'd' && v.gunner && v.gunner.faction !== me.faction))) continue;   // you only join your own team's car
      if ((v.type !== 'turret' && Math.abs((v.y || 0) - me.y) > 3) || (v.team && match.mode === 'tdm' && v.team !== me.faction)) continue;   // an enemy base's sentry is not yours to man
      const d = distToVehicle(v, me.x, me.z); if (d <= (seat === 'g' && v.driver ? VEH.gunRange : VEH.useRange) && d < bd) { best = v; bd = d; gun = seat === 'g'; }   // the roof seat of a moving car can be taken from a bit further away
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
    if (!v || v.dead || !d || !me.alive || me.seat || now - me.lastVeh < 15) return;
    if (![d.x, d.z, d.yaw, d.speed].every(n => typeof n === 'number' && Number.isFinite(n))) return;
    me.lastVeh = now;
    if (v.type === 'turret') { v.yaw = r3(wrap(d.yaw)); if (Number.isFinite(d.pitch)) me.pitch = r3(clamp(d.pitch, -1.2, 1.2)); me.x = v.x; me.z = v.z; me.y = v.sy; v.dirty = true; return; }   // a pillar gun only turns
    const T = vd(v), limX = (map.ex || map.half) - T.hx, limZ = (map.ez || map.half) - T.hx;
    v.x = r2(clamp(d.x, -limX, limX)); v.z = r2(clamp(d.z, -limZ, limZ)); v.yaw = r3(wrap(d.yaw)); v.speed = r2(clamp(d.speed, -T.maxReverse, T.maxSpeed));
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

  on('loadout', d => {   // choose which three weapons you carry (keys 1-3): only ones your level has unlocked
    const now = Date.now(); if (!d || now - me.shopAt < 150) return; me.shopAt = now;
    if (!Number.isInteger(d.slot) || d.slot < 0 || d.slot > 2 || !Number.isInteger(d.wi) || d.wi < 0 || d.wi >= WEAPONS.length) return;
    if (WEAPONS[d.wi].pickupOnly) return notice(me, 'The ' + WEAPONS[d.wi].name + ' can only be found on the map');
    if (lvOf(me) < WEAPONS[d.wi].unlockLevel) return notice(me, WEAPONS[d.wi].name + ' unlocks at level ' + WEAPONS[d.wi].unlockLevel);
    const pr = profOf(me), lo = cleanLoadout(pr.eq.loadout).slice(); lo[d.slot] = d.wi; pr.eq.loadout = lo; pr.rev++; store.set(me.token, pr);
    me.loadout = loadoutOf(me); me.sock.emit('profile', profileView(me)); notice(me, WEAPONS[d.wi].name + ' is now on key ' + (d.slot + 1) + (me.alive ? ' (ready when you respawn)' : ''));
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

  on('getprofile', id => {   // somebody opened another player's profile: send what is public (bots get a believable one too)
    const now = Date.now(); if (typeof id !== 'number' || now - (me.profAt || 0) < 250) return; me.profAt = now;
    const t = [...players.values()].find(q => q.id === id); if (t) socket.emit('pubprofile', pubProfile(t));
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
  if (match.state === 'live' && match.endsAt && now >= match.endsAt) timeUp();
  for (const p of players.values()) if (p.alive && p.burnUntil > now && now >= (p.burnNext || 0)) { p.burnNext = now + 500; hurt(p.burnBy || p, p, Math.max(1, Math.round(p.burnDps / 2)), false, 'burn'); }   // on fire
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

if (require.main !== module) module.exports = { navFor, navPath, navLine, MAPS, validateMap, surfaceY, rayRamp, rayBox, rampY, clientMap, rooms, inRoom, createRoom, cast, applyHit, hurt, takePickup, WEAPONS, tickVehicles, tickTurrets, heatOk, VWEAPONS };   // lets the tests reach the geometry helpers
