/* ═══════════════════════════════════════════════════════════════
   ChickenRun — Crash Betting Game Engine  (v3 full rewrite)

   RULES:
   ─ 8 vertical lanes. Chicken crosses left→right.
   ─ Fixed multipliers per lane: 1x, 1.2x, 1.5x, 2x, 2.5x, 3x, 3.5x, 4x
   ─ Algorithm decides a crash lane (1–8) or 0 = safe (chicken reaches finish).
   ─ If a lane is SAFE: cars clear out / speed away BEFORE chicken enters.
     No car is present while chicken crosses that lane.
   ─ If a lane is the CRASH lane: a car is timed to HIT the chicken mid-crossing.
   ─ Cars in non-active lanes drive normally but NEVER overlap each other.
   ─ Between lanes chicken rests 2s, crossing takes 2s.

   ALGORITHM (house-edge):
   ─ 60% pot → payout pool (+rollover).  40% → profit (split 40/30/30).
   ─ Simulate payouts lane-by-lane; when pool exhausted → crash lane.
   ═══════════════════════════════════════════════════════════════ */

// ───── POLYFILL ─────
if (!CanvasRenderingContext2D.prototype.roundRect) {
  CanvasRenderingContext2D.prototype.roundRect = function (x, y, w, h, r) {
    r = Math.min(typeof r === "number" ? r : (r?.[0] ?? 0), w / 2, h / 2);
    this.moveTo(x + r, y);
    this.arcTo(x + w, y, x + w, y + h, r);
    this.arcTo(x + w, y + h, x, y + h, r);
    this.arcTo(x, y + h, x, y, r);
    this.arcTo(x, y, x + w, y, r);
    this.closePath();
    return this;
  };
}

// ═══════════════════════════════════════
//  CONFIG
// ═══════════════════════════════════════
const LANE_MULTS = [1.0, 1.2, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0]; // fixed per lane
const LANE_COUNT = LANE_MULTS.length; // 8

const CFG = {
  BETTING_TIME: 15, // seconds
  WAITING_TIME: 5,
  CROSS_TIME: 2000, // ms chicken takes to cross one lane
  REST_TIME: 2000, // ms chicken rests between lanes
  SAFE_ZONE_PCT: 0.09, // canvas % for each safe zone
  BASE_PAYOUT_PCT: 0.6,
  PROFIT_PLATFORM: 0.4,
  PROFIT_PROVIDER: 0.3,
  PROFIT_ROLLOVER: 0.3,
  MIN_BOTS: 8,
  MAX_BOTS: 18,
  START_BALANCE: 1000,
  CAR_BASE_SPEED: 2.5, // base px/frame (at 60fps equiv)
  CAR_FAST_MULT: 3.0, // speed multiplier when clearing lane
};

// ═══════════════════════════════════════
//  STATE
// ═══════════════════════════════════════
const ST = {
  phase: "idle", // idle | betting | waiting | playing | crashed | finished
  round: 0,
  balance: CFG.START_BALANCE,
  bet: 0,
  hasBet: false,
  cashedOut: false,
  cashoutLane: 0, // which lane user cashed out after (0 = didn't)
  cashoutMult: 0,
  cashoutAmount: 0,
  currentLane: 0, // 0=start zone, 1-8=crossing/crossed lane N
  crashLane: 0, // 0=no crash (safe all 8), 1-8=crash at lane N
  isCrossing: false,
  crossProgress: 0, // 0..1
  splatActive: false,
  bots: [],
  rollover: 0,
  history: [],
  totalBet: 0,
  totalWin: 0,
  totalLoss: 0,
  // Round stats
  rPot: 0,
  rPool: 0,
  rPlatProfit: 0,
  rProvFee: 0,
  rRollover: 0,
  rBonus: 0,
  // Car system — one car per lane, fully orchestrated
  laneCars: [], // array[8] of car objects (one per lane)
};

// ═══════════════════════════════════════
//  PERSISTENCE
// ═══════════════════════════════════════
const SAVE_KEY = "chickenrun_v3";
function save() {
  localStorage.setItem(
    SAVE_KEY,
    JSON.stringify({
      balance: ST.balance,
      totalBet: ST.totalBet,
      totalWin: ST.totalWin,
      totalLoss: ST.totalLoss,
      rollover: ST.rollover,
      history: ST.history.slice(-40),
      round: ST.round,
    }),
  );
}
function load() {
  try {
    const d = JSON.parse(localStorage.getItem(SAVE_KEY));
    if (!d) return;
    ST.balance = d.balance ?? CFG.START_BALANCE;
    ST.totalBet = d.totalBet ?? 0;
    ST.totalWin = d.totalWin ?? 0;
    ST.totalLoss = d.totalLoss ?? 0;
    ST.rollover = d.rollover ?? 0;
    ST.history = d.history ?? [];
    ST.round = d.round ?? 0;
  } catch (e) {
    /* */
  }
}
function resetAll() {
  localStorage.removeItem(SAVE_KEY);
  ST.balance = CFG.START_BALANCE;
  ST.totalBet = 0;
  ST.totalWin = 0;
  ST.totalLoss = 0;
  ST.rollover = 0;
  ST.history = [];
  ST.round = 0;
  DOM.historyItems.innerHTML = "";
  updateUI();
}
function addBal() {
  ST.balance += 1000;
  save();
  updateUI();
}

// ═══════════════════════════════════════
//  DOM
// ═══════════════════════════════════════
const $ = (s) => document.querySelector(s);
const $$ = (s) => document.querySelectorAll(s);
const DOM = {};
let ctx;

function cacheDom() {
  const ids = [
    "game-canvas",
    "game-overlay",
    "overlay-icon",
    "overlay-title",
    "overlay-subtitle",
    "multiplier-display",
    "mult-value",
    "cashout-popup",
    "cashout-amount",
    "crash-popup",
    "crash-at",
    "phase-display",
    "phase-text",
    "balance-value",
    "bet-input",
    "action-btn",
    "action-text",
    "round-number",
    "players-count",
    "live-bets-body",
    "history-items",
    "stat-total-bet",
    "stat-total-win",
    "stat-total-loss",
    "stat-net",
    "stat-pot",
    "stat-pool",
    "stat-platform-profit",
    "stat-provider-fee",
    "stat-rollover",
    "stat-bonus",
    "reset-btn",
    "add-balance-btn",
  ];
  ids.forEach((id) => {
    const key = id.replace(/-([a-z])/g, (_, c) => c.toUpperCase());
    DOM[key] = document.getElementById(id);
  });
  // aliases
  DOM.canvas = DOM.gameCanvas;
  DOM.overlay = DOM.gameOverlay;
  DOM.multDisplay = DOM.multiplierDisplay;
}

// ═══════════════════════════════════════
//  HELPERS
// ═══════════════════════════════════════
const rand = (a, b) => Math.floor(Math.random() * (b - a + 1)) + a;
const randF = (a, b) => Math.random() * (b - a) + a;
const fmt = (n) =>
  n.toLocaleString("en-US", {
    minimumFractionDigits: 2,
    maximumFractionDigits: 2,
  });
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const lerp = (a, b, t) => a + (b - a) * t;

function randomName() {
  const c = "bcdfghjklmnpqrstvwxyz",
    v = "aeiou";
  let n = "";
  for (let i = 0, len = rand(5, 9); i < len; i++)
    n += (i % 2 === 0 ? c : v)[rand(0, (i % 2 === 0 ? c : v).length - 1)];
  n = n[0].toUpperCase() + n.slice(1);
  if (Math.random() > 0.5) n += rand(1, 99);
  return n;
}

// ═══════════════════════════════════════
//  BOT GENERATION
// ═══════════════════════════════════════
function genBots() {
  const n = rand(CFG.MIN_BOTS, CFG.MAX_BOTS);
  const bets = [
    50, 50, 100, 100, 100, 200, 200, 300, 500, 500, 1000, 2000, 5000,
  ];
  const bots = [];
  for (let i = 0; i < n; i++) {
    // targetLane: which lane they want to cash out AFTER (1-8, 8=ride all)
    let tl;
    const r = Math.random();
    if (r < 0.3)
      tl = rand(1, 2); // 30% cash early
    else if (r < 0.55)
      tl = rand(3, 4); // 25%
    else if (r < 0.75)
      tl = rand(5, 6); // 20%
    else if (r < 0.9)
      tl = rand(7, 7); // 15%
    else tl = 8; // 10% ride full
    bots.push({
      id: String(rand(100000, 999999)),
      username: randomName(),
      betAmount: bets[rand(0, bets.length - 1)],
      targetLane: tl,
      status: "waiting",
      cashoutMult: 0,
      cashoutAmount: 0,
    });
  }
  return bots;
}

// ═══════════════════════════════════════
//  ALGORITHM — Determine crash lane
// ═══════════════════════════════════════
function calcCrashLane(bots, realBet) {
  /**
   * Total pot → 60% payout pool (+ rollover from prev round)
   * Simulate lane by lane:
   *   At each lane, bots whose targetLane <= laneIndex cash out.
   *   Subtract their payout from pool.
   *   Also consider worst-case real user cashout.
   *   If pool goes negative → this lane is the crash lane.
   * If pool survives all 8 lanes → crashLane = 0 (safe).
   */
  const botSum = bots.reduce((s, b) => s + b.betAmount, 0);
  const pot = botSum + realBet;
  const pool0 = pot * CFG.BASE_PAYOUT_PCT + ST.rollover;
  const profit = pot * (1 - CFG.BASE_PAYOUT_PCT);

  ST.rPot = pot;
  ST.rPool = pool0;
  ST.rPlatProfit = profit * CFG.PROFIT_PLATFORM;
  ST.rProvFee = profit * CFG.PROFIT_PROVIDER;
  ST.rRollover = profit * CFG.PROFIT_ROLLOVER;
  ST.rBonus = 0;

  let poolLeft = pool0;
  let crashLane = 0; // 0 = survives all

  for (let lane = 1; lane <= LANE_COUNT; lane++) {
    const mult = LANE_MULTS[lane - 1];
    // Bot payouts at this lane
    let lanePayout = 0;
    bots.forEach((b) => {
      if (b.targetLane === lane) lanePayout += b.betAmount * (1 + mult);
    });
    // Worst case: real user also cashes here
    const realWorst = realBet > 0 ? realBet * (1 + mult) : 0;

    if (poolLeft - lanePayout - realWorst < 0) {
      crashLane = lane;
      break;
    }
    poolLeft -= lanePayout;
    if (poolLeft < 0) {
      crashLane = lane;
      break;
    }
  }

  // Drama: 12% chance crash 1 lane earlier
  if (crashLane === 0 && Math.random() < 0.12) {
    crashLane = rand(6, 8);
  } else if (crashLane > 2 && Math.random() < 0.1) {
    crashLane = Math.max(1, crashLane - 1);
  }
  // 4% instant crash at lane 1
  if (Math.random() < 0.04) crashLane = 1;

  if (crashLane < 0) crashLane = 0;
  if (crashLane > LANE_COUNT) crashLane = LANE_COUNT;

  // Set rollover for next round
  ST.rollover = ST.rRollover;
  return crashLane;
}

// ═══════════════════════════════════════
//  LAYOUT — positions from canvas size
// ═══════════════════════════════════════
function getLayout(w, h) {
  const sw = w * CFG.SAFE_ZONE_PCT;
  const rl = sw,
    rr = w - sw;
  const rw = rr - rl;
  const lw = rw / LANE_COUNT;
  const centers = [];
  for (let i = 0; i < LANE_COUNT; i++) centers.push(rl + lw * i + lw / 2);
  // Chicken stop X positions: 0=left safe, 1..8=right edge of each lane
  const stops = [sw / 2];
  for (let i = 0; i < LANE_COUNT; i++) stops.push(rl + lw * (i + 1));
  return { sw, rl, rr, rw, lw, centers, stops, w, h };
}

// ═══════════════════════════════════════
//  CAR SYSTEM — One car per lane, orchestrated
//
//  Each lane has exactly ONE car driving vertically.
//  Cars never overlap because they're each in their own lane.
//
//  Car states per lane:
//    'driving'  — normal speed, looping top↔bottom
//    'clearing' — chicken approaching, car speeds away to clear lane
//    'gone'     — lane empty, chicken crossing safely
//    'striking' — car timed to hit chicken mid-lane (crash lane)
//    'idle'     — waiting, car drives normally in background
// ═══════════════════════════════════════
const CAR_COLORS = [
  "#E74C3C",
  "#3498DB",
  "#2ECC71",
  "#F39C12",
  "#9B59B6",
  "#1ABC9C",
  "#E67E22",
  "#ff6b9d",
];
const TRUCK_COLORS = ["#6b7280", "#374151", "#7c3aed", "#dc2626"];

function initLaneCars(layout) {
  ST.laneCars = [];
  for (let i = 0; i < LANE_COUNT; i++) {
    const dir = i % 2 === 0 ? 1 : -1;
    const isTruck = Math.random() < 0.25;
    const vW = isTruck ? rand(26, 32) : rand(20, 26);
    const vH = isTruck ? rand(52, 66) : rand(38, 50);
    ST.laneCars.push({
      lane: i,
      dir,
      isTruck,
      vW,
      vH,
      color: isTruck
        ? TRUCK_COLORS[rand(0, TRUCK_COLORS.length - 1)]
        : CAR_COLORS[rand(0, CAR_COLORS.length - 1)],
      x: layout.centers[i],
      y:
        dir === 1
          ? randF(-layout.h * 0.3, layout.h * 0.6)
          : randF(layout.h * 0.3, layout.h * 1.3),
      speed: CFG.CAR_BASE_SPEED * (isTruck ? 0.7 : 1) * dir,
      state: "driving", // driving | clearing | gone | striking
    });
  }
}

function updateCar(car, layout, dt) {
  const h = layout.h;
  const spd =
    car.state === "clearing" ? car.speed * CFG.CAR_FAST_MULT : car.speed;

  car.x = layout.centers[car.lane]; // track lane center on resize
  car.y += spd * (dt / 16);

  // Wrap around
  if (car.state !== "gone" && car.state !== "striking") {
    if (car.dir === 1 && car.y > h + car.vH) car.y = -car.vH;
    if (car.dir === -1 && car.y < -car.vH) car.y = h + car.vH;
  }

  // 'clearing' → once off-screen, become 'gone'
  if (car.state === "clearing") {
    if (
      (car.dir === 1 && car.y > h + car.vH + 20) ||
      (car.dir === -1 && car.y < -car.vH - 20)
    ) {
      car.state = "gone";
    }
  }
}

// Make car enter for a crash strike
function setupStrike(car, layout, chickenY) {
  car.state = "striking";
  // Position car off-screen, aimed to arrive at chickenY when chicken is mid-lane
  // Car enters from its direction side at double speed
  const strikeSpeed = Math.abs(car.speed) * CFG.CAR_FAST_MULT * 0.7;
  const travelTime = CFG.CROSS_TIME * 0.5; // arrive at 50% crossing progress
  const distance = strikeSpeed * (travelTime / 16); // frames at 60fps ≈ dt=16

  if (car.dir === 1) {
    car.y = chickenY - distance;
  } else {
    car.y = chickenY + distance;
  }
  car.speed = Math.abs(car.speed) * CFG.CAR_FAST_MULT * 0.7 * car.dir;
}

// ═══════════════════════════════════════
//  CANVAS RESIZE
// ═══════════════════════════════════════
function resizeCanvas() {
  const box = DOM.canvas.parentElement.getBoundingClientRect();
  const dpr = window.devicePixelRatio || 1;
  DOM.canvas.width = box.width * dpr;
  DOM.canvas.height = box.height * dpr;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  DOM.canvas._w = box.width;
  DOM.canvas._h = box.height;
}

// ═══════════════════════════════════════
//  DRAWING
// ═══════════════════════════════════════
function shade(color, d) {
  let n = parseInt(color.replace("#", ""), 16);
  let r = clamp((n >> 16) + d, 0, 255);
  let g = clamp(((n >> 8) & 0xff) + d, 0, 255);
  let b = clamp((n & 0xff) + d, 0, 255);
  return "#" + ((1 << 24) + (r << 16) + (g << 8) + b).toString(16).slice(1);
}

function drawRoad(L, t) {
  const { w, h, sw, rl, rr, lw, centers } = L;

  // Grass zones
  let g = ctx.createLinearGradient(0, 0, sw, 0);
  g.addColorStop(0, "#1a4d1a");
  g.addColorStop(1, "#2d6a2d");
  ctx.fillStyle = g;
  ctx.fillRect(0, 0, sw, h);
  g = ctx.createLinearGradient(rr, 0, w, 0);
  g.addColorStop(0, "#2d6a2d");
  g.addColorStop(1, "#1a4d1a");
  ctx.fillStyle = g;
  ctx.fillRect(rr, 0, sw, h);

  // Grass dots
  ctx.fillStyle = "#3a8a3a";
  for (let i = 0; i < 30; i++) {
    ctx.fillRect((i * 11.3) % sw, (i * 23.7 + t * 0.004) % h, 2, 2);
    ctx.fillRect(rr + ((i * 14.1) % sw), (i * 31.2 + t * 0.004) % h, 2, 2);
  }

  // Labels
  const fs = clamp(sw * 0.26, 8, 14);
  ctx.font = `bold ${fs}px 'Chakra Petch', sans-serif`;
  ctx.textAlign = "center";
  ctx.fillStyle = "#f7c948";
  ctx.save();
  ctx.translate(sw / 2, h / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.fillText("▶  START", 0, 0);
  ctx.restore();
  ctx.fillStyle = "#22c55e";
  ctx.save();
  ctx.translate(rr + sw / 2, h / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.fillText("🏁 FINISH", 0, 0);
  ctx.restore();

  // Road
  ctx.fillStyle = "#333";
  ctx.fillRect(rl, 0, rr - rl, h);

  // Road edges
  ctx.strokeStyle = "rgba(255,255,255,0.6)";
  ctx.lineWidth = 3;
  ctx.beginPath();
  ctx.moveTo(rl, 0);
  ctx.lineTo(rl, h);
  ctx.stroke();
  ctx.beginPath();
  ctx.moveTo(rr, 0);
  ctx.lineTo(rr, h);
  ctx.stroke();

  // Lane dividers + multiplier labels
  const dash = 22,
    gap = 14,
    off = (t * 0.025) % (dash + gap);
  for (let i = 0; i < LANE_COUNT; i++) {
    // Right edge divider (skip last)
    if (i < LANE_COUNT - 1) {
      const x = rl + (i + 1) * lw;
      ctx.strokeStyle = "rgba(247,201,72,0.22)";
      ctx.lineWidth = 2;
      ctx.setLineDash([dash, gap]);
      ctx.lineDashOffset = -off;
      ctx.beginPath();
      ctx.moveTo(x, 0);
      ctx.lineTo(x, h);
      ctx.stroke();
      ctx.setLineDash([]);
    }
    // Direction arrow
    const d = i % 2 === 0 ? 1 : -1;
    ctx.fillStyle = "rgba(255,255,255,0.05)";
    ctx.font = `${clamp(lw * 0.3, 10, 20)}px sans-serif`;
    ctx.textAlign = "center";
    const arrow = d === 1 ? "▼" : "▲";
    for (let row = 0; row < 4; row++) {
      const ay = (((row * h) / 3 + t * 0.02 * d + 9999) % (h + 50)) - 25;
      ctx.fillText(arrow, centers[i], ay);
    }
    // Multiplier label at top of each lane
    ctx.fillStyle = "rgba(255,255,255,0.12)";
    ctx.font = `bold ${clamp(lw * 0.22, 9, 14)}px 'JetBrains Mono', monospace`;
    ctx.fillText(`${LANE_MULTS[i]}x`, centers[i], 18);
  }
}

function drawVehicle(car) {
  if (car.state === "gone") return;
  const { x, y, vW, vH, color, dir, isTruck } = car;
  ctx.save();
  ctx.translate(x, y);
  if (dir === -1) ctx.scale(1, -1);
  const hw = vW / 2,
    hh = vH / 2;

  if (isTruck) {
    ctx.fillStyle = shade(color, 15);
    ctx.beginPath();
    ctx.roundRect(-hw, -hh, vW, vH * 0.38, 5);
    ctx.fill();
    ctx.fillStyle = "rgba(120,200,255,0.4)";
    ctx.fillRect(-hw * 0.55, -hh + 3, vW * 0.55, vH * 0.15);
    ctx.fillStyle = color;
    ctx.beginPath();
    ctx.roundRect(-hw, -hh + vH * 0.35, vW, vH * 0.65, 3);
    ctx.fill();
    ctx.fillStyle = shade(color, 25);
    ctx.fillRect(-hw + 2, -hh + vH * 0.55, vW - 4, 2);
  } else {
    ctx.fillStyle = color;
    ctx.beginPath();
    ctx.roundRect(-hw, -hh, vW, vH, 5);
    ctx.fill();
    ctx.fillStyle = shade(color, -25);
    ctx.beginPath();
    ctx.roundRect(-hw * 0.7, -hh + vH * 0.22, vW * 0.7, vH * 0.48, 4);
    ctx.fill();
    ctx.fillStyle = "rgba(120,200,255,0.35)";
    ctx.fillRect(-hw * 0.5, -hh + 3, vW * 0.5, vH * 0.15);
    ctx.fillStyle = "#F7C948";
    ctx.beginPath();
    ctx.arc(-hw * 0.45, -hh + 3, 2.5, 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.arc(hw * 0.45, -hh + 3, 2.5, 0, Math.PI * 2);
    ctx.fill();
    ctx.fillStyle = "#E74C3C";
    ctx.beginPath();
    ctx.arc(-hw * 0.45, hh - 3, 2, 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.arc(hw * 0.45, hh - 3, 2, 0, Math.PI * 2);
    ctx.fill();
  }
  // Wheels
  ctx.fillStyle = "#111";
  ctx.fillRect(-hw - 2, -hh + vH * 0.1, 4, 7);
  ctx.fillRect(-hw - 2, hh - vH * 0.1 - 7, 4, 7);
  ctx.fillRect(hw - 2, -hh + vH * 0.1, 4, 7);
  ctx.fillRect(hw - 2, hh - vH * 0.1 - 7, 4, 7);
  ctx.restore();
}

function drawChicken(x, y, sz, splat) {
  ctx.save();
  ctx.translate(x, y);
  if (splat) {
    ctx.globalAlpha = 0.9;
    ctx.fillStyle = "#E74C3C";
    for (let i = 0; i < 10; i++) {
      const a = (i / 10) * Math.PI * 2,
        d = sz * (0.5 + Math.sin(i * 3.7) * 0.35);
      ctx.beginPath();
      ctx.arc(Math.cos(a) * d, Math.sin(a) * d, sz * 0.11, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.fillStyle = "#F7C948";
    for (let i = 0; i < 7; i++) {
      const a = (i / 7) * Math.PI * 2 + 0.4,
        d = sz * (0.25 + Math.sin(i * 4.3) * 0.25);
      ctx.beginPath();
      ctx.ellipse(
        Math.cos(a) * d,
        Math.sin(a) * d,
        sz * 0.09,
        sz * 0.04,
        a,
        0,
        Math.PI * 2,
      );
      ctx.fill();
    }
    ctx.strokeStyle = "#222";
    ctx.lineWidth = 3;
    ctx.beginPath();
    ctx.moveTo(-6, -6);
    ctx.lineTo(6, 6);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(6, -6);
    ctx.lineTo(-6, 6);
    ctx.stroke();
    ctx.globalAlpha = 1;
    ctx.restore();
    return;
  }
  // Shadow
  ctx.fillStyle = "rgba(0,0,0,0.15)";
  ctx.beginPath();
  ctx.ellipse(1, sz * 0.4, sz * 0.28, sz * 0.07, 0, 0, Math.PI * 2);
  ctx.fill();
  // Body
  ctx.fillStyle = "#F7C948";
  ctx.beginPath();
  ctx.ellipse(0, 0, sz * 0.3, sz * 0.36, 0, 0, Math.PI * 2);
  ctx.fill();
  ctx.strokeStyle = "#CFA020";
  ctx.lineWidth = 1;
  ctx.stroke();
  // Wing
  ctx.fillStyle = "#E6B800";
  ctx.beginPath();
  ctx.ellipse(-sz * 0.05, sz * 0.04, sz * 0.14, sz * 0.09, 0.2, 0, Math.PI * 2);
  ctx.fill();
  // Head
  ctx.fillStyle = "#F7C948";
  ctx.beginPath();
  ctx.arc(sz * 0.25, -sz * 0.14, sz * 0.18, 0, Math.PI * 2);
  ctx.fill();
  ctx.strokeStyle = "#CFA020";
  ctx.lineWidth = 1;
  ctx.stroke();
  // Eye
  ctx.fillStyle = "#1a1a2e";
  ctx.beginPath();
  ctx.arc(sz * 0.32, -sz * 0.18, sz * 0.03, 0, Math.PI * 2);
  ctx.fill();
  ctx.fillStyle = "#fff";
  ctx.beginPath();
  ctx.arc(sz * 0.34, -sz * 0.2, sz * 0.012, 0, Math.PI * 2);
  ctx.fill();
  // Beak
  ctx.fillStyle = "#E67E22";
  ctx.beginPath();
  ctx.moveTo(sz * 0.41, -sz * 0.16);
  ctx.lineTo(sz * 0.52, -sz * 0.12);
  ctx.lineTo(sz * 0.41, -sz * 0.08);
  ctx.closePath();
  ctx.fill();
  // Comb
  ctx.fillStyle = "#E74C3C";
  ctx.beginPath();
  ctx.arc(sz * 0.22, -sz * 0.3, sz * 0.05, 0, Math.PI * 2);
  ctx.fill();
  ctx.beginPath();
  ctx.arc(sz * 0.29, -sz * 0.32, sz * 0.04, 0, Math.PI * 2);
  ctx.fill();
  // Feet
  ctx.strokeStyle = "#D4780A";
  ctx.lineWidth = 1.5;
  [-0.05, 0.1].forEach((ox) => {
    const bx = sz * ox;
    ctx.beginPath();
    ctx.moveTo(bx, sz * 0.32);
    ctx.lineTo(bx, sz * 0.46);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(bx, sz * 0.46);
    ctx.lineTo(bx - 3, sz * 0.5);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(bx, sz * 0.46);
    ctx.lineTo(bx + 3, sz * 0.5);
    ctx.stroke();
  });
  ctx.restore();
}

// ═══════════════════════════════════════
//  RENDER LOOP
// ═══════════════════════════════════════
let prevTs = 0,
  anim = 0;

function render(ts) {
  const dt = ts - prevTs;
  prevTs = ts;
  anim += dt;
  const w = DOM.canvas._w,
    h = DOM.canvas._h;
  if (!w || !h) {
    requestAnimationFrame(render);
    return;
  }

  ctx.clearRect(0, 0, w, h);
  const L = getLayout(w, h);

  drawRoad(L, anim);

  // Update & draw lane cars
  ST.laneCars.forEach((car) => {
    updateCar(car, L, dt);
    drawVehicle(car);
  });

  // Chicken
  const sz = clamp(Math.min(w, h) * 0.06, 16, 40);
  const cy = h / 2;

  if (
    ST.phase === "playing" ||
    ST.phase === "crashed" ||
    ST.phase === "finished"
  ) {
    let cx;
    if (ST.isCrossing && ST.currentLane >= 1) {
      const from = L.stops[ST.currentLane - 1];
      const to = L.stops[ST.currentLane];
      cx = lerp(from, to, ST.crossProgress);
    } else {
      cx = L.stops[ST.currentLane] ?? L.stops[0];
    }
    const hop = ST.isCrossing ? Math.sin(ST.crossProgress * Math.PI) * -8 : 0;
    drawChicken(cx, cy + hop, sz, ST.splatActive);
  } else {
    const bob = Math.sin(anim * 0.003) * 2;
    drawChicken(L.stops[0], cy + bob, sz, false);
  }

  requestAnimationFrame(render);
}

// ═══════════════════════════════════════
//  UI
// ═══════════════════════════════════════
function updateUI() {
  DOM.balanceValue.textContent = fmt(ST.balance);
  DOM.roundNumber.textContent = `Round #${ST.round}`;
  DOM.statTotalBet.textContent = `$${fmt(ST.totalBet)}`;
  DOM.statTotalWin.textContent = `$${fmt(ST.totalWin)}`;
  DOM.statTotalLoss.textContent = `$${fmt(ST.totalLoss)}`;
  const net = ST.totalWin - ST.totalLoss;
  DOM.statNet.textContent = `${net >= 0 ? "+" : "-"}$${fmt(Math.abs(net))}`;
  DOM.statNet.style.color = net >= 0 ? "var(--green)" : "var(--red)";
  DOM.statPot.textContent = `$${fmt(ST.rPot)}`;
  DOM.statPool.textContent = `$${fmt(ST.rPool)}`;
  DOM.statPlatformProfit.textContent = `$${fmt(ST.rPlatProfit)}`;
  DOM.statProviderFee.textContent = `$${fmt(ST.rProvFee)}`;
  DOM.statRollover.textContent = `$${fmt(ST.rollover)}`;
  DOM.statBonus.textContent = `$${fmt(ST.rBonus)}`;
}

function setPhase(p, t) {
  ST.phase = p;
  DOM.phaseText.textContent = t || p.toUpperCase();
  DOM.phaseDisplay.className = `phase-badge ${p}`;
}
function showOverlay(icon, title, sub) {
  DOM.overlay.classList.remove("hidden");
  DOM.overlayIcon.textContent = icon;
  DOM.overlayTitle.textContent = title;
  DOM.overlaySubtitle.innerHTML = sub;
}
function hideOverlay() {
  DOM.overlay.classList.add("hidden");
}

function updateTable() {
  const all = [];
  if (ST.hasBet) {
    all.push({
      username: "★ YOU ★",
      betAmount: ST.bet,
      status: ST.cashedOut
        ? "cashed"
        : ST.phase === "crashed"
          ? "crashed"
          : "waiting",
      cashoutMult: ST.cashedOut ? ST.cashoutMult : 0,
      cashoutAmount: ST.cashedOut ? ST.cashoutAmount : 0,
      isYou: true,
    });
  }
  ST.bots.forEach((b) => all.push({ ...b, isYou: false }));
  DOM.playersCount.textContent = `${all.length} players`;
  let html = "";
  all.forEach((p) => {
    let st,
      mt = "-";
    if (p.status === "cashed") {
      st = `<span class="status-cashed">+$${fmt(p.cashoutAmount)}</span>`;
      mt = `${p.cashoutMult.toFixed(1)}x`;
    } else if (p.status === "crashed") {
      st = `<span class="status-crashed">Crashed</span>`;
    } else {
      st = `<span class="status-waiting">Waiting</span>`;
    }
    html += `<tr class="${p.isYou ? "you" : ""}"><td>${p.isYou ? "★ YOU" : p.username}</td><td>$${fmt(p.betAmount)}</td><td>${mt}</td><td>${st}</td></tr>`;
  });
  DOM.liveBetsBody.innerHTML = html;
}

function addHistory(mult) {
  const el = document.createElement("div");
  el.className =
    "history-chip " + (mult < 1.5 ? "low" : mult < 3 ? "mid" : "high");
  el.textContent = `${mult.toFixed(1)}x`;
  DOM.historyItems.prepend(el);
  while (DOM.historyItems.children.length > 40)
    DOM.historyItems.removeChild(DOM.historyItems.lastChild);
}

// ═══════════════════════════════════════
//  GAME LOOP
// ═══════════════════════════════════════
async function gameLoop() {
  while (true) {
    await phaseBetting();
    await phaseWaiting();
    await phasePlaying();
    await phasePost();
  }
}

async function phaseBetting() {
  ST.round++;
  ST.hasBet = false;
  ST.cashedOut = false;
  ST.bet = 0;
  ST.currentLane = 0;
  ST.isCrossing = false;
  ST.crossProgress = 0;
  ST.splatActive = false;
  ST.crashLane = 0;
  ST.bots = genBots();

  // Init cars for visual
  const L = getLayout(DOM.canvas._w, DOM.canvas._h);
  initLaneCars(L);

  setPhase("betting", "BETTING");
  showOverlay(
    "🐔",
    "PLACE YOUR BETS",
    `Round starts in <span id="countdown">${CFG.BETTING_TIME}</span>s`,
  );

  DOM.actionBtn.disabled = false;
  DOM.actionBtn.className = "action-btn bet-btn";
  DOM.actionText.textContent = "PLACE BET";
  DOM.betInput.disabled = false;
  DOM.cashoutPopup.classList.add("hidden");
  DOM.crashPopup.classList.add("hidden");
  DOM.multDisplay.classList.add("hidden");

  updateTable();
  updateUI();

  for (let t = CFG.BETTING_TIME; t > 0; t--) {
    const el = document.getElementById("countdown");
    if (el) el.textContent = t;
    await sleep(1000);
  }
}

async function phaseWaiting() {
  setPhase("waiting", "CALCULATING");
  showOverlay("⏳", "CALCULATING...", "Preparing next round");
  DOM.actionBtn.disabled = true;
  DOM.betInput.disabled = true;

  ST.crashLane = calcCrashLane(ST.bots, ST.hasBet ? ST.bet : 0);
  console.log(
    `[R${ST.round}] crashLane=${ST.crashLane} (${ST.crashLane > 0 ? LANE_MULTS[ST.crashLane - 1] + "x" : "SAFE"}) pot=$${ST.rPot.toFixed(0)}`,
  );
  updateUI();

  for (let t = CFG.WAITING_TIME; t > 0; t--) {
    DOM.overlaySubtitle.innerHTML = `Starting in <span>${t}</span>s...`;
    await sleep(1000);
  }
}

async function phasePlaying() {
  setPhase("playing", "LIVE");
  hideOverlay();
  DOM.multDisplay.classList.remove("hidden");

  if (ST.hasBet) {
    DOM.actionBtn.disabled = false;
    DOM.actionBtn.className = "action-btn cashout-btn";
    DOM.actionText.textContent = "CASHOUT";
  }

  const L = getLayout(DOM.canvas._w, DOM.canvas._h);
  const chickenY = DOM.canvas._h / 2;

  // Cross each lane 1..8
  for (let lane = 1; lane <= LANE_COUNT; lane++) {
    const mult = LANE_MULTS[lane - 1];
    const isCrashLane = ST.crashLane === lane;
    const carIdx = lane - 1;
    const car = ST.laneCars[carIdx];

    // Update multiplier display
    DOM.multValue.textContent = `${mult}x`;
    DOM.multValue.className =
      "mult-value" + (mult >= 3 ? " danger" : mult >= 2 ? " high" : "");

    if (ST.hasBet && !ST.cashedOut) {
      DOM.actionText.textContent = `CASHOUT $${fmt(ST.bet * (1 + mult))}`;
    }

    // ── PREPARE LANE ──
    if (isCrashLane) {
      // Set up the striking car — it will arrive when chicken is mid-lane
      setupStrike(car, L, chickenY);
    } else {
      // Clear the lane: car speeds away before chicken crosses
      car.state = "clearing";
    }

    // Wait a beat for car to clear (or for strike car to get ready)
    if (!isCrashLane) {
      // Wait until car is gone (max 800ms)
      const clearStart = performance.now();
      while (car.state !== "gone" && performance.now() - clearStart < 800) {
        await sleep(16);
      }
      car.state = "gone"; // force
    } else {
      await sleep(100); // tiny pause before crossing into crash lane
    }

    // ── CROSSING (2s) ──
    ST.currentLane = lane;
    ST.isCrossing = true;
    ST.crossProgress = 0;
    const t0 = performance.now();
    await new Promise((resolve) => {
      (function tick() {
        const e = performance.now() - t0;
        ST.crossProgress = clamp(e / CFG.CROSS_TIME, 0, 1);
        if (e >= CFG.CROSS_TIME) {
          ST.crossProgress = 1;
          resolve();
        } else requestAnimationFrame(tick);
      })();
    });
    ST.isCrossing = false;

    // ── CRASH? ──
    if (isCrashLane) {
      ST.splatActive = true;
      doCrash(mult);
      return; // exit playing phase
    }

    // ── SAFE — rest phase (2s) ──
    // Process bot cashouts
    ST.bots.forEach((b) => {
      if (b.status === "waiting" && b.targetLane <= lane) {
        b.status = "cashed";
        b.cashoutMult = mult;
        b.cashoutAmount = b.betAmount * (1 + mult);
      }
    });
    updateTable();

    await sleep(CFG.REST_TIME);
  }

  // ── SURVIVED ALL 8 LANES ──
  doFinish();
}

function doCrash(mult) {
  let bonus = 0;
  ST.bots.forEach((b) => {
    if (b.status === "waiting") {
      b.status = "crashed";
      bonus += b.betAmount;
    }
  });
  if (ST.hasBet && !ST.cashedOut) {
    ST.totalLoss += ST.bet;
    bonus += ST.bet;
    save();
  }
  ST.rBonus = bonus;

  DOM.crashPopup.classList.remove("hidden");
  DOM.crashAt.textContent = `@ ${mult}x`;
  DOM.multValue.textContent = `${mult}x`;
  DOM.multValue.className = "mult-value danger";
  DOM.actionBtn.disabled = true;

  setPhase("crashed", `CRASHED @ ${mult}x`);
  ST.history.push(mult);
  addHistory(mult);
  updateTable();
  updateUI();
}

function doFinish() {
  // Chicken made it! All remaining bots cash out at 4x
  ST.bots.forEach((b) => {
    if (b.status === "waiting") {
      b.status = "cashed";
      b.cashoutMult = LANE_MULTS[LANE_COUNT - 1];
      b.cashoutAmount = b.betAmount * (1 + LANE_MULTS[LANE_COUNT - 1]);
    }
  });
  // If user still riding, they win at 4x
  if (ST.hasBet && !ST.cashedOut) {
    ST.cashedOut = true;
    ST.cashoutMult = LANE_MULTS[LANE_COUNT - 1];
    ST.cashoutAmount = ST.bet * (1 + ST.cashoutMult);
    ST.balance += ST.cashoutAmount;
    ST.totalWin += ST.cashoutAmount;
    DOM.cashoutPopup.classList.remove("hidden");
    DOM.cashoutAmount.textContent = `+$${fmt(ST.cashoutAmount)}`;
    setTimeout(() => DOM.cashoutPopup.classList.add("hidden"), 3000);
    save();
  }

  DOM.multValue.textContent = `${LANE_MULTS[LANE_COUNT - 1]}x 🏁`;
  DOM.multValue.className = "mult-value high";
  DOM.actionBtn.disabled = true;
  setPhase("finished", "SAFE — 4.0x");
  ST.history.push(LANE_MULTS[LANE_COUNT - 1]);
  addHistory(LANE_MULTS[LANE_COUNT - 1]);
  updateTable();
  updateUI();
}

async function phasePost() {
  await sleep(4000);
  ST.splatActive = false;
  DOM.crashPopup.classList.add("hidden");
  DOM.cashoutPopup.classList.add("hidden");
  DOM.multDisplay.classList.add("hidden");
  save();
}

// ═══════════════════════════════════════
//  USER ACTIONS
// ═══════════════════════════════════════
function placeBet() {
  if (ST.phase !== "betting") return;
  const a = parseFloat(DOM.betInput.value);
  if (isNaN(a) || a < 10 || a > ST.balance) {
    DOM.actionBtn.style.animation = "shake 0.4s ease";
    setTimeout(() => (DOM.actionBtn.style.animation = ""), 400);
    return;
  }
  ST.bet = a;
  ST.hasBet = true;
  ST.balance -= a;
  ST.totalBet += a;
  DOM.actionBtn.disabled = true;
  DOM.actionText.textContent = "BET PLACED ✓";
  DOM.betInput.disabled = true;
  updateTable();
  updateUI();
  save();
}

function cashout() {
  if (ST.phase !== "playing" || !ST.hasBet || ST.cashedOut) return;
  const lane = ST.currentLane;
  const mult = lane >= 1 ? LANE_MULTS[lane - 1] : 0;
  ST.cashedOut = true;
  ST.cashoutLane = lane;
  ST.cashoutMult = mult;
  ST.cashoutAmount = ST.bet * (1 + mult);
  ST.balance += ST.cashoutAmount;
  ST.totalWin += ST.cashoutAmount;

  DOM.cashoutPopup.classList.remove("hidden");
  DOM.cashoutAmount.textContent = `+$${fmt(ST.cashoutAmount)}`;
  DOM.actionBtn.disabled = true;
  DOM.actionText.textContent = "CASHED OUT ✓";
  DOM.actionBtn.className = "action-btn bet-btn";
  setTimeout(() => DOM.cashoutPopup.classList.add("hidden"), 2500);
  updateTable();
  updateUI();
  save();
}

// ═══════════════════════════════════════
//  EVENTS
// ═══════════════════════════════════════
function initEvents() {
  DOM.actionBtn.addEventListener("click", () => {
    if (ST.phase === "betting" && !ST.hasBet) placeBet();
    else if (ST.phase === "playing" && ST.hasBet && !ST.cashedOut) cashout();
  });
  $$(".chip").forEach((c) =>
    c.addEventListener("click", () => {
      if (ST.phase !== "betting" || ST.hasBet) return;
      DOM.betInput.value = Math.min(
        (parseFloat(DOM.betInput.value) || 0) + parseInt(c.dataset.value),
        Math.floor(ST.balance),
      );
    }),
  );
  $$(".quick-btn").forEach((b) =>
    b.addEventListener("click", () => {
      if (ST.phase !== "betting" || ST.hasBet) return;
      let v = parseFloat(DOM.betInput.value) || 0;
      switch (b.dataset.action) {
        case "half":
          DOM.betInput.value = Math.max(10, Math.floor(v / 2));
          break;
        case "double":
          DOM.betInput.value = Math.min(Math.floor(ST.balance), v * 2);
          break;
        case "max":
          DOM.betInput.value = Math.floor(ST.balance);
          break;
        case "clear":
          DOM.betInput.value = 0;
          break;
      }
    }),
  );
  DOM.resetBtn.addEventListener("click", () => {
    if (confirm("Reset ALL data and stats?")) resetAll();
  });
  DOM.addBalanceBtn.addEventListener("click", addBal);
  document.addEventListener("keydown", (e) => {
    if (
      e.code === "Space" &&
      ST.phase === "playing" &&
      ST.hasBet &&
      !ST.cashedOut
    ) {
      e.preventDefault();
      cashout();
    }
  });
  window.addEventListener("resize", resizeCanvas);
}

// ═══════════════════════════════════════
//  BOOT
// ═══════════════════════════════════════
document.addEventListener("DOMContentLoaded", () => {
  cacheDom();
  ctx = DOM.canvas.getContext("2d");
  load();
  ST.history.forEach((m) => addHistory(m));
  resizeCanvas();
  updateUI();
  initEvents();
  // Init cars for idle animation
  const L = getLayout(DOM.canvas._w, DOM.canvas._h);
  initLaneCars(L);
  requestAnimationFrame(render);
  gameLoop();
});
