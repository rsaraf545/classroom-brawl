const http = require('http');
const fs   = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');
const os   = require('os');

const PORT        = process.env.PORT || 4000;
const TICK_RATE   = 60;
const W           = 960;
const H           = 640;
const P_RADIUS    = 15;
const BULLET_SPEED = 9;
const BULLET_LIFE  = 22;   // short range: ~198px
const BULLET_LIFE_LONG = 110;
const PLAYER_SPEED = 3.4;
const FURY_SPEED   = 5.0;
const DASH_SPEED   = 11;
const DASH_FRAMES  = 9;
const DASH_CD      = 150;  // 2.5s
const MAX_HP       = 5;
const WIN_SCORE    = 10;
const SHOOT_CD     = 20;
const FURY_SHOOT_CD = 10;
const RESPAWN_T    = 180;
const INVULN_T     = 90;   // 1.5s spawn protection
const DOUBLE_KILL_WINDOW = 240; // 4s

const SHIELD_DURATION  = 300;
const FURY_DURATION    = 300;
const LONGBOW_DURATION = 300;

const COLORS = ['#4fb8ff', '#ff4444', '#50e878', '#ffb833', '#cc66ff', '#ff66aa', '#33ffee', '#ffee33'];
const SPAWNS = [
  { x: 160, y: 320 }, { x: 800, y: 320 },
  { x: 480, y: 140 }, { x: 480, y: 500 },
  { x: 160, y: 140 }, { x: 800, y: 500 },
  { x: 800, y: 140 }, { x: 160, y: 500 },
];

const OBSTACLES = [
  { x: 230, y: 150, w: 90,  h: 22 },
  { x: 640, y: 150, w: 90,  h: 22 },
  { x: 400, y: 250, w: 160, h: 22 },
  { x: 110, y: 360, w: 22,  h: 120 },
  { x: 828, y: 360, w: 22,  h: 120 },
  { x: 265, y: 470, w: 110, h: 22 },
  { x: 585, y: 470, w: 110, h: 22 },
  { x: 400, y: 360, w: 22,  h: 90 },
  { x: 230, y: 310, w: 70,  h: 22 },
  { x: 660, y: 310, w: 70,  h: 22 },
];

const POWERUP_ALTARS = [
  { x: 480, y: 320 },
  { x: 300, y: 220 },
  { x: 660, y: 220 },
  { x: 300, y: 430 },
  { x: 660, y: 430 },
  { x: 480, y: 130 },
  { x: 480, y: 510 },
];

const POWERUP_TYPES = ['aegis', 'ares', 'ambrosia', 'longbow'];

// ── Helpers ───────────────────────────────────────────────
function circleVsRect(cx, cy, r, rx, ry, rw, rh) {
  const nx = Math.max(rx, Math.min(cx, rx + rw));
  const ny = Math.max(ry, Math.min(cy, ry + rh));
  return Math.hypot(cx - nx, cy - ny) < r;
}
function obsBlock(x, y, r) {
  return OBSTACLES.some(o => circleVsRect(x, y, r, o.x, o.y, o.w, o.h));
}
function inBounds(x, y, r) {
  return x - r > 0 && x + r < W && y - r > 0 && y + r < H;
}

// ── State ─────────────────────────────────────────────────
let players  = new Map();
let bullets  = [];
let powerups = [];
let nextId   = 1;
const usedSlots = new Set();
let nextPuId = 1;
let gameState = 'waiting';
let winner    = null;
let tick      = 0;
let puSpawnTimer = 120;
let firstBloodTaken = false;
let tickEvents = []; // FX events sent to clients each tick

function claimSlot() {
  for (let i = 0; i < COLORS.length; i++) {
    if (!usedSlots.has(i)) { usedSlots.add(i); return i; }
  }
  return -1;
}

function makePlayer(id, idx) {
  const sp = SPAWNS[idx % SPAWNS.length];
  return {
    id, name: `P${id}`,
    color: COLORS[idx % COLORS.length],
    x: sp.x, y: sp.y, startX: sp.x, startY: sp.y,
    angle: 0,
    hp: MAX_HP, score: 0,
    shootCD: 0, hitFlash: 0,
    alive: true, respawnTimer: 0,
    shieldTimer: 0, furyTimer: 0, longbowTimer: 0,
    invulnTimer: 0,
    dashCD: 0, dashTimer: 0, dashVx: 0, dashVy: 0,
    killStreak: 0, lastKillAt: -99999,
    keys: { up: false, down: false, left: false, right: false, shoot: false, dash: false },
  };
}

function resetAll() {
  gameState = 'playing';
  winner = null;
  bullets = [];
  powerups = [];
  puSpawnTimer = 180;
  firstBloodTaken = false;
  for (const p of players.values()) {
    Object.assign(p, {
      hp: MAX_HP, score: 0,
      alive: true, respawnTimer: 0, hitFlash: 0, shootCD: 0,
      shieldTimer: 0, furyTimer: 0, longbowTimer: 0,
      invulnTimer: 0, dashCD: 0, dashTimer: 0,
      killStreak: 0, lastKillAt: -99999,
      x: p.startX, y: p.startY, angle: 0,
      keys: { up: false, down: false, left: false, right: false, shoot: false, dash: false },
    });
  }
}

function spawnPowerup() {
  const occupied = new Set(powerups.map(p => `${p.x},${p.y}`));
  const free = POWERUP_ALTARS.filter(a => !occupied.has(`${a.x},${a.y}`));
  if (free.length === 0) return;
  const altar = free[Math.floor(Math.random() * free.length)];
  const type  = POWERUP_TYPES[Math.floor(Math.random() * POWERUP_TYPES.length)];
  powerups.push({ id: nextPuId++, x: altar.x, y: altar.y, type });
}

function streakName(n) {
  if (n >= 7) return 'GODLIKE';
  if (n === 6) return 'UNSTOPPABLE';
  if (n === 5) return 'RAMPAGE';
  if (n === 4) return 'DOMINATING';
  if (n === 3) return 'KILLING SPREE';
  return null;
}

// ── Game loop ─────────────────────────────────────────────
setInterval(() => {
  tick++;
  if (gameState !== 'playing') return;

  const all = [...players.values()];

  if (powerups.length < 3) {
    if (--puSpawnTimer <= 0) {
      puSpawnTimer = 360;
      spawnPowerup();
    }
  }

  for (const p of all) {
    if (!p.alive) {
      if (--p.respawnTimer <= 0) {
        p.alive = true; p.hp = MAX_HP;
        p.x = p.startX; p.y = p.startY;
        p.hitFlash = 0; p.shieldTimer = 0; p.furyTimer = 0; p.longbowTimer = 0;
        p.invulnTimer = INVULN_T;
        tickEvents.push({ t: 'respawn', x: p.x, y: p.y, color: p.color });
      }
      continue;
    }

    if (p.hitFlash     > 0) p.hitFlash--;
    if (p.shootCD      > 0) p.shootCD--;
    if (p.shieldTimer  > 0) p.shieldTimer--;
    if (p.furyTimer    > 0) p.furyTimer--;
    if (p.longbowTimer > 0) p.longbowTimer--;
    if (p.invulnTimer  > 0) p.invulnTimer--;
    if (p.dashCD       > 0) p.dashCD--;

    const k = p.keys;
    let dx = (k.right ? 1 : 0) - (k.left ? 1 : 0);
    let dy = (k.down  ? 1 : 0) - (k.up   ? 1 : 0);

    // Dash activation
    if (k.dash && p.dashCD === 0 && p.dashTimer === 0) {
      let ang = p.angle;
      if (dx || dy) ang = Math.atan2(dy, dx);
      p.dashTimer = DASH_FRAMES;
      p.dashCD    = DASH_CD;
      p.dashVx = Math.cos(ang) * DASH_SPEED;
      p.dashVy = Math.sin(ang) * DASH_SPEED;
      p.angle  = ang;
      tickEvents.push({ t: 'dash', x: p.x, y: p.y, angle: ang, color: p.color });
    }

    if (p.dashTimer > 0) {
      p.dashTimer--;
      dx = p.dashVx; dy = p.dashVy;
    } else if (dx || dy) {
      const len  = Math.hypot(dx, dy);
      const spd  = p.furyTimer > 0 ? FURY_SPEED : PLAYER_SPEED;
      dx = dx / len * spd;
      dy = dy / len * spd;
      p.angle = Math.atan2(dy, dx);
    }

    const nx = p.x + dx;
    if (inBounds(nx, p.y, P_RADIUS) && !obsBlock(nx, p.y, P_RADIUS + 1)) p.x = nx;
    const ny = p.y + dy;
    if (inBounds(p.x, ny, P_RADIUS) && !obsBlock(p.x, ny, P_RADIUS + 1)) p.y = ny;

    const cd = p.furyTimer > 0 ? FURY_SHOOT_CD : SHOOT_CD;
    if (k.shoot && p.shootCD === 0) {
      p.shootCD = cd;
      p.invulnTimer = 0; // shooting breaks spawn protection
      const bx = p.x + Math.cos(p.angle) * (P_RADIUS + 7);
      const by = p.y + Math.sin(p.angle) * (P_RADIUS + 7);
      bullets.push({
        x: bx, y: by,
        vx: Math.cos(p.angle) * BULLET_SPEED,
        vy: Math.sin(p.angle) * BULLET_SPEED,
        angle: p.angle,
        ownerId: p.id, ownerColor: p.color,
        fury:    p.furyTimer    > 0,
        longbow: p.longbowTimer > 0,
        life: p.longbowTimer > 0 ? BULLET_LIFE_LONG : BULLET_LIFE,
      });
      tickEvents.push({ t: 'shot', x: bx, y: by, angle: p.angle, color: p.color });
    }

    for (let i = powerups.length - 1; i >= 0; i--) {
      const pu = powerups[i];
      if (Math.hypot(p.x - pu.x, p.y - pu.y) < P_RADIUS + 20) {
        if (pu.type === 'aegis')    p.shieldTimer  = SHIELD_DURATION;
        if (pu.type === 'ares')     p.furyTimer    = FURY_DURATION;
        if (pu.type === 'ambrosia') p.hp = Math.min(MAX_HP, p.hp + 2);
        if (pu.type === 'longbow')  p.longbowTimer = LONGBOW_DURATION;
        tickEvents.push({ t: 'pickup', x: pu.x, y: pu.y, type: pu.type, color: p.color });
        powerups.splice(i, 1);
      }
    }
  }

  for (let i = bullets.length - 1; i >= 0; i--) {
    const b = bullets[i];
    b.x += b.vx; b.y += b.vy; b.life--;
    b.angle = Math.atan2(b.vy, b.vx);

    let dead = b.life <= 0 || !inBounds(b.x, b.y, 5);
    if (!dead && OBSTACLES.some(o => b.x > o.x && b.x < o.x + o.w && b.y > o.y && b.y < o.y + o.h)) {
      dead = true;
      tickEvents.push({ t: 'wallhit', x: b.x, y: b.y, color: b.ownerColor });
    }

    if (!dead) {
      for (const p of all) {
        if (p.id === b.ownerId || !p.alive) continue;
        if (p.invulnTimer > 0) continue; // spawn protection: bullets pass through
        if (Math.hypot(p.x - b.x, p.y - b.y) < P_RADIUS + 5) {
          dead = true;
          if (p.shieldTimer > 0) {
            tickEvents.push({ t: 'deflect', x: b.x, y: b.y });
            break;
          }
          p.hp--; p.hitFlash = 14;
          tickEvents.push({ t: 'hit', x: b.x, y: b.y, color: p.color, victimId: p.id });
          if (p.hp <= 0) {
            p.alive = false; p.respawnTimer = RESPAWN_T;
            p.killStreak = 0;
            const owner = all.find(pl => pl.id === b.ownerId);
            if (owner) {
              owner.score++;
              owner.killStreak++;
              const isDouble = (tick - owner.lastKillAt) <= DOUBLE_KILL_WINDOW;
              owner.lastKillAt = tick;
              const ev = {
                t: 'death', x: p.x, y: p.y,
                victimColor: p.color, victimName: p.name,
                killerColor: owner.color, killerName: owner.name, killerId: owner.id,
              };
              if (!firstBloodTaken) { ev.firstBlood = true; firstBloodTaken = true; }
              if (isDouble) ev.double = true;
              const sn = streakName(owner.killStreak);
              if (sn) ev.streak = sn;
              tickEvents.push(ev);
              if (owner.score >= WIN_SCORE) {
                gameState = 'gameover';
                winner = { id: owner.id, name: owner.name, color: owner.color, score: owner.score };
              }
            }
          }
          break;
        }
      }
    }
    if (dead) bullets.splice(i, 1);
  }

  const payload = {
    type: 'state', gameState, winner, tick,
    players: all.map(({ id, name, color, x, y, angle, hp, score, alive, respawnTimer, hitFlash, shieldTimer, furyTimer, longbowTimer, invulnTimer, dashCD, killStreak }) =>
      ({ id, name, color, x, y, angle, hp, score, alive, respawnTimer, hitFlash, shieldTimer, furyTimer, longbowTimer, invulnTimer, dashCD, killStreak })
    ),
    bullets: bullets.map(({ x, y, angle, ownerColor, fury, longbow, life }) => ({ x, y, angle, ownerColor, fury, longbow, life })),
    powerups: powerups.map(({ id, x, y, type }) => ({ id, x, y, type })),
  };
  if (tickEvents.length) payload.events = tickEvents;
  broadcast(payload);
  tickEvents = [];

}, 1000 / TICK_RATE);

// ── HTTP ──────────────────────────────────────────────────
const server = http.createServer((req, res) => {
  if (req.url === '/' || req.url === '/index.html') {
    res.writeHead(200, { 'Content-Type': 'text/html' });
    fs.createReadStream(path.join(__dirname, 'client.html')).pipe(res);
  } else {
    res.writeHead(404); res.end();
  }
});

const wss = new WebSocketServer({ server });

wss.on('connection', ws => {
  const slot = claimSlot();
  if (slot === -1) {
    ws.send(JSON.stringify({ type: 'full' })); ws.close(); return;
  }
  const p = makePlayer(nextId++, slot);
  p.slot = slot;
  players.set(ws, p);
  console.log(`+ ${p.name} (${p.color}) joined — ${players.size} online`);

  ws.send(JSON.stringify({
    type: 'assigned', id: p.id, name: p.name, color: p.color,
    obstacles: OBSTACLES, W, H,
  }));
  broadcast({ type: 'lobby', count: players.size });

  if (players.size >= 2 && gameState === 'waiting') {
    gameState = 'playing';
    firstBloodTaken = false;
    console.log('⚔  Battle started!');
  }

  ws.on('message', raw => {
    try {
      const msg = JSON.parse(raw);
      if (msg.type === 'input')   p.keys = msg.keys;
      if (msg.type === 'restart' && gameState === 'gameover') resetAll();
    } catch {}
  });

  ws.on('close', () => {
    players.delete(ws);
    usedSlots.delete(p.slot);
    console.log(`- ${p.name} left — ${players.size} online`);
    if (players.size < 2 && gameState === 'playing') gameState = 'waiting';
    if (gameState === 'gameover' && players.size < 2) {
      gameState = 'waiting'; winner = null; bullets = []; powerups = [];
    }
    broadcast({ type: 'lobby', count: players.size });
  });
});

function broadcast(data) {
  const msg = JSON.stringify(data);
  for (const ws of players.keys())
    if (ws.readyState === 1) ws.send(msg);
}

server.listen(PORT, '0.0.0.0', () => {
  const nets = os.networkInterfaces();
  console.log('\n  ⚔  CLASSROOM BRAWL — TROY EDITION\n');
  console.log(`  Local:   http://localhost:${PORT}`);
  for (const list of Object.values(nets))
    for (const n of list)
      if (n.family === 'IPv4' && !n.internal)
        console.log(`  Network: http://${n.address}:${PORT}  ← share this with classmates`);
  console.log('\n  Waiting for warriors...\n');
});
