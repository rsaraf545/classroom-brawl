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
const PLAYER_SPEED = 3.4;
const FURY_SPEED   = 5.0;
const MAX_HP       = 5;
const WIN_SCORE    = 10;
const SHOOT_CD     = 20;
const FURY_SHOOT_CD = 10;
const RESPAWN_T    = 180;

const SHIELD_DURATION  = 300;  // 5s
const FURY_DURATION    = 300;  // 5s
const LONGBOW_DURATION = 300;  // 5s
const BULLET_LIFE_LONG = 110;  // full range when buffed

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

// Power-up altar positions (fixed spots on the map)
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
const usedSlots = new Set(); // track which color/spawn slots are in use
let nextPuId = 1;
let gameState = 'waiting';
let winner    = null;
let tick      = 0;
let puSpawnTimer = 120; // first spawn in 2s

function claimSlot() {
  for (let i = 0; i < COLORS.length; i++) {
    if (!usedSlots.has(i)) { usedSlots.add(i); return i; }
  }
  return -1; // full
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
    shieldTimer: 0,
    furyTimer: 0,
    longbowTimer: 0,
    keys: { up: false, down: false, left: false, right: false, shoot: false },
  };
}

function resetAll() {
  gameState = 'playing';
  winner = null;
  bullets = [];
  powerups = [];
  puSpawnTimer = 180;
  for (const p of players.values()) {
    Object.assign(p, {
      hp: MAX_HP, score: 0,
      alive: true, respawnTimer: 0, hitFlash: 0, shootCD: 0,
      shieldTimer: 0, furyTimer: 0, longbowTimer: 0,
      x: p.startX, y: p.startY, angle: 0,
      keys: { up: false, down: false, left: false, right: false, shoot: false },
    });
  }
}

// ── Powerup spawning ──────────────────────────────────────
function spawnPowerup() {
  const occupied = new Set(powerups.map(p => `${p.x},${p.y}`));
  const free = POWERUP_ALTARS.filter(a => !occupied.has(`${a.x},${a.y}`));
  if (free.length === 0) return;
  const altar = free[Math.floor(Math.random() * free.length)];
  const type  = POWERUP_TYPES[Math.floor(Math.random() * POWERUP_TYPES.length)];
  powerups.push({ id: nextPuId++, x: altar.x, y: altar.y, type, pulse: 0 });
}

// ── Game loop ─────────────────────────────────────────────
setInterval(() => {
  if (gameState !== 'playing') { tick++; return; }
  tick++;

  const all = [...players.values()];

  // Spawn power-ups
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
        p.hitFlash = 0; p.shieldTimer = 0; p.furyTimer = 0;
      }
      continue;
    }

    if (p.hitFlash     > 0) p.hitFlash--;
    if (p.shootCD      > 0) p.shootCD--;
    if (p.shieldTimer  > 0) p.shieldTimer--;
    if (p.furyTimer    > 0) p.furyTimer--;
    if (p.longbowTimer > 0) p.longbowTimer--;

    const k = p.keys;
    let dx = (k.right ? 1 : 0) - (k.left ? 1 : 0);
    let dy = (k.down  ? 1 : 0) - (k.up   ? 1 : 0);

    if (dx || dy) {
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
      bullets.push({
        x:  p.x + Math.cos(p.angle) * (P_RADIUS + 7),
        y:  p.y + Math.sin(p.angle) * (P_RADIUS + 7),
        vx: Math.cos(p.angle) * BULLET_SPEED,
        vy: Math.sin(p.angle) * BULLET_SPEED,
        ownerId: p.id, ownerColor: p.color,
        fury:    p.furyTimer    > 0,
        longbow: p.longbowTimer > 0,
        life: p.longbowTimer > 0 ? BULLET_LIFE_LONG : BULLET_LIFE,
      });
    }

    // Collect power-ups
    for (let i = powerups.length - 1; i >= 0; i--) {
      const pu = powerups[i];
      if (Math.hypot(p.x - pu.x, p.y - pu.y) < P_RADIUS + 20) {
        if (pu.type === 'aegis')    p.shieldTimer   = SHIELD_DURATION;
        if (pu.type === 'ares')     p.furyTimer     = FURY_DURATION;
        if (pu.type === 'ambrosia') p.hp = Math.min(MAX_HP, p.hp + 2);
        if (pu.type === 'longbow')  p.longbowTimer  = LONGBOW_DURATION;
        powerups.splice(i, 1);
      }
    }
  }

  // Bullets
  for (let i = bullets.length - 1; i >= 0; i--) {
    const b = bullets[i];
    b.x += b.vx; b.y += b.vy; b.life--;

    let dead = b.life <= 0 || !inBounds(b.x, b.y, 5)
      || OBSTACLES.some(o => b.x > o.x && b.x < o.x + o.w && b.y > o.y && b.y < o.y + o.h);

    if (!dead) {
      for (const p of all) {
        if (p.id === b.ownerId || !p.alive) continue;
        if (Math.hypot(p.x - b.x, p.y - b.y) < P_RADIUS + 5) {
          dead = true;
          if (p.shieldTimer > 0) break; // aegis deflects
          p.hp--; p.hitFlash = 14;
          if (p.hp <= 0) {
            p.alive = false; p.respawnTimer = RESPAWN_T;
            const owner = all.find(pl => pl.id === b.ownerId);
            if (owner && ++owner.score >= WIN_SCORE) {
              gameState = 'gameover';
              winner = { id: owner.id, name: owner.name, color: owner.color, score: owner.score };
            }
          }
          break;
        }
      }
    }
    if (dead) bullets.splice(i, 1);
  }

  broadcast({
    type: 'state', gameState, winner, tick,
    players: all.map(({ id, name, color, x, y, angle, hp, score, alive, respawnTimer, hitFlash, shieldTimer, furyTimer, longbowTimer }) =>
      ({ id, name, color, x, y, angle, hp, score, alive, respawnTimer, hitFlash, shieldTimer, furyTimer, longbowTimer })
    ),
    bullets: bullets.map(({ x, y, ownerColor, fury, life }) => ({ x, y, ownerColor, fury, life })),
    powerups: powerups.map(({ id, x, y, type }) => ({ id, x, y, type })),
  });

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
  p.slot = slot; // remember so we can free it on disconnect
  players.set(ws, p);
  console.log(`+ ${p.name} (${p.color}) joined — ${players.size} online`);

  ws.send(JSON.stringify({
    type: 'assigned', id: p.id, name: p.name, color: p.color,
    obstacles: OBSTACLES, W, H,
  }));
  broadcast({ type: 'lobby', count: players.size });

  if (players.size >= 2 && gameState === 'waiting') {
    gameState = 'playing';
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
    usedSlots.delete(p.slot); // free the slot so a new joiner can reuse it
    console.log(`- ${p.name} left — ${players.size} online`);
    if (players.size < 2 && gameState === 'playing') gameState = 'waiting';
    // Also reset gameover so returning players get a fresh game
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
