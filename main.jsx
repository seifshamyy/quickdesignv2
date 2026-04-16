import React, { useState, useReducer, useRef, useEffect, useCallback } from 'react';
import {
  Pencil, SquareDashedBottom as SquareDashed, DoorClosed, AppWindow, Refrigerator, Box,
  Undo, Redo, Trash2, Box as Box3D, BoxSelect, Minus, MousePointer2,
  Maximize2, ChevronLeft, ChevronRight, Download, Upload, Save,
  AlertTriangle, Info, ZoomIn, ZoomOut, Camera,
} from 'lucide-react';

// =============================================================================
// CONSTANTS
// =============================================================================
const GRID = 5;
const WALL_T = 15;
const WALL_H = 250;
const MAX_HIST = 50;

// Wall endpoint snap radius in SCREEN pixels (zoom-independent)
const ENDPOINT_SNAP_PX = 20;

// Wall-mount magnetic assist radius — how close cursor must be to a wall
// for element placement to magnetize. NOT a gate — ghost always shows.
const MOUNT_MAGNET = 50;

const DRAW_TOOLS = ['wall', 'virtual_wall', 'short_wall', 'base_cab', 'upper_cab'];
// Only these tools get endpoint-snap behavior
const ENDPOINT_SNAP_TOOLS = ['wall', 'virtual_wall', 'short_wall'];

const ITEMS = {
  fridge:   { w: 80,  d: 80, h: 200, color: '#94a3b8', name: 'Fridge',   mount: 'against' },
  sink:     { w: 80,  d: 60, h: 90,  color: '#d97706', name: 'Sink',     mount: 'against' },
  stove:    { w: 80,  d: 60, h: 90,  color: '#374151', name: 'Stove',    mount: 'against' },
  cupboard: { w: 90,  d: 55, h: 210, color: '#a16207', name: 'Cupboard', mount: 'against' },
  door:     { w: 90,  d: WALL_T, h: 200, color: '#8b4513', name: 'Door',   mount: 'inside' },
  window:   { w: 100, d: WALL_T, h: 100, color: '#38bdf8', name: 'Window', mount: 'inside', elev: 100 },
};

const TOOL_DEFS = [
  { key: 'select',       icon: <MousePointer2 size={18} />, label: 'Select',       sc: 'V',  group: 'Tools' },
  { key: 'wall',         icon: <Pencil size={18} />,        label: 'Wall',         sc: 'W',  group: 'Build' },
  { key: 'short_wall',   icon: <Minus size={18} />,         label: 'Short Wall',   sc: null, group: 'Build' },
  { key: 'virtual_wall', icon: <SquareDashed size={18} />,  label: 'Virtual Wall', sc: null, group: 'Build' },
  { key: 'base_cab',     icon: <Box size={18} />,           label: 'Base Cab',     sc: null, group: 'Cabinetry' },
  { key: 'upper_cab',    icon: <BoxSelect size={18} />,     label: 'Upper Cab',    sc: null, group: 'Cabinetry' },
  { key: 'door',         icon: <DoorClosed size={18} />,    label: 'Door',         sc: 'D',  group: 'Elements' },
  { key: 'window',       icon: <AppWindow size={18} />,     label: 'Window',       sc: 'I',  group: 'Elements' },
  { key: 'fridge',       icon: <Refrigerator size={18} />,  label: 'Fridge',       sc: 'F',  group: 'Elements' },
  { key: 'sink',         icon: <Box size={18} />,           label: 'Sink',         sc: 'S',  group: 'Elements' },
  { key: 'stove',        icon: <Box size={18} />,           label: 'Stove',        sc: null, group: 'Elements' },
  { key: 'cupboard',     icon: <DoorClosed size={18} />,    label: 'Cupboard',     sc: 'C',  group: 'Elements' },
];

// =============================================================================
// MATH HELPERS
// =============================================================================
let _idc = 0;
const uid = () => `e${++_idc}_${(Math.random() * 46656 | 0).toString(36)}`;
const gridSnap = v => Math.round(v / GRID) * GRID;

const ptSeg = (px, py, x1, y1, x2, y2) => {
  const l2 = (x1 - x2) ** 2 + (y1 - y2) ** 2;
  if (l2 === 0) return { t: 0, x: x1, y: y1, dist: Math.hypot(px - x1, py - y1) };
  let t = ((px - x1) * (x2 - x1) + (py - y1) * (y2 - y1)) / l2;
  t = Math.max(0, Math.min(1, t));
  const nx = x1 + t * (x2 - x1), ny = y1 + t * (y2 - y1);
  return { t, x: nx, y: ny, dist: Math.hypot(px - nx, py - ny) };
};

const checkOverlap = (px, py, r, x1, y1, x2, y2, thresh) => {
  const l2 = (x1 - x2) ** 2 + (y1 - y2) ** 2;
  if (l2 === 0) return Math.hypot(px - x1, py - y1) < r;
  let t = ((px - x1) * (x2 - x1) + (py - y1) * (y2 - y1)) / l2;
  const pjx = x1 + t * (x2 - x1), pjy = y1 + t * (y2 - y1);
  if (Math.hypot(px - pjx, py - pjy) > thresh) return false;
  const tr = r / Math.sqrt(l2);
  return t >= -tr && t <= 1 + tr;
};

const dynOffset = (x1, y1, x2, y2, mx, my, depth) => {
  const dx = x2 - x1, dy = y2 - y1, len = Math.hypot(dx, dy);
  if (len === 0) return { sx: 0, sy: 0 };
  let nx = -dy / len, ny = dx / len;
  if ((mx - x1) * nx + (my - y1) * ny < 0) { nx = -nx; ny = -ny; }
  const s = WALL_T / 2 + depth / 2;
  return { sx: nx * s, sy: ny * s };
};

const wallThick = t => t === 'short' || t === 'base_cab' ? 60 : t === 'upper_cab' ? 30 : t === 'virtual' ? 2 : WALL_T;

const polyArea = pts => {
  let a = 0;
  for (let i = 0; i < pts.length; i++) {
    const j = (i + 1) % pts.length;
    a += pts[i].x * pts[j].y - pts[j].x * pts[i].y;
  }
  return Math.abs(a) / 2;
};

const detectRooms = walls => {
  const sw = walls.filter(w => w.type === 'solid');
  if (sw.length < 3) return [];
  const eps = 25, pts = [];
  const getP = (x, y) => {
    for (let i = 0; i < pts.length; i++) if (Math.hypot(pts[i].x - x, pts[i].y - y) < eps) return i;
    pts.push({ x, y }); return pts.length - 1;
  };
  const adj = {};
  sw.forEach(w => {
    const a = getP(w.x1, w.y1), b = getP(w.x2, w.y2);
    (adj[a] ??= new Set()).add(b); (adj[b] ??= new Set()).add(a);
  });
  const rooms = [], seen = new Set();
  for (let start = 0; start < pts.length; start++) {
    if (!adj[start] || adj[start].size < 2) continue;
    for (const fs of adj[start]) {
      const queue = [[fs, [start, fs]]], visited = new Set([start, fs]);
      let found = false;
      while (queue.length && !found) {
        const [cur, path] = queue.shift();
        if (path.length > 7) continue;
        for (const next of (adj[cur] ?? [])) {
          if (next === start && path.length >= 3) {
            const key = [...path].sort((a, b) => a - b).join(',');
            if (!seen.has(key)) { seen.add(key); rooms.push(path.map(i => pts[i])); }
            found = true; break;
          }
          if (!visited.has(next) && path.length < 7) { visited.add(next); queue.push([next, [...path, next]]); }
        }
      }
    }
  }
  return rooms.filter(r => r.length >= 3 && r.length <= 6).slice(0, 4);
};

const centroid = pts => ({
  x: pts.reduce((s, p) => s + p.x, 0) / pts.length,
  y: pts.reduce((s, p) => s + p.y, 0) / pts.length,
});

// =============================================================================
// REDUCER
// =============================================================================
const INIT = { walls: [], elements: [], sel: null, past: [], future: [] };

function reducer(st, act) {
  const snap_ = () => structuredClone({ walls: st.walls, elements: st.elements });
  const push = (w, e) => ({ ...st, walls: w, elements: e, past: [...st.past, snap_()].slice(-MAX_HIST), future: [] });

  switch (act.type) {
    case 'ADD_WALL': return push([...st.walls, act.p], st.elements);
    case 'ADD_EL': return push(st.walls, [...st.elements, act.p]);
    case 'UPD_WALL': return push(st.walls.map(w => w.id === act.p.id ? { ...w, ...act.p } : w), st.elements);
    case 'UPD_EL': return push(st.walls, st.elements.map(e => e.id === act.p.id ? { ...e, ...act.p } : e));
    case 'DEL_WALL': return { ...push(st.walls.filter(w => w.id !== act.p), st.elements), sel: null };
    case 'DEL_EL': return { ...push(st.walls, st.elements.filter(e => e.id !== act.p)), sel: null };
    case 'SEL': return { ...st, sel: act.p };
    case 'DESEL': return { ...st, sel: null };
    case 'UNDO': {
      if (!st.past.length) return st;
      const prev = st.past.at(-1);
      return { ...st, walls: prev.walls, elements: prev.elements, past: st.past.slice(0, -1), future: [snap_(), ...st.future].slice(0, MAX_HIST), sel: null };
    }
    case 'REDO': {
      if (!st.future.length) return st;
      const next = st.future[0];
      return { ...st, walls: next.walls, elements: next.elements, past: [...st.past, snap_()].slice(-MAX_HIST), future: st.future.slice(1), sel: null };
    }
    case 'CLEAR': return { ...push([], []), sel: null };
    case 'LOAD': return { ...INIT, walls: act.p.walls ?? [], elements: act.p.elements ?? [] };
    default: return st;
  }
}

// =============================================================================
// VALIDATION (preserved from original)
// =============================================================================
const validateLine = (s, e, tt, els) => {
  if (tt === 'upper_cab')
    return !els.some(el => el.type === 'window' && checkOverlap(el.x, el.y, ITEMS.window.w / 2 - 5, s.x, s.y, e.x, e.y, 15 + ITEMS.window.w / 2));
  if (tt === 'base_cab' || tt === 'short_wall')
    return !els.some(el => ['fridge', 'sink', 'door'].includes(el.type) && checkOverlap(el.x, el.y, ITEMS[el.type].w / 2 - 5, s.x, s.y, e.x, e.y, 30 + ITEMS[el.type].w / 2));
  return true;
};

const validateGhost = (g, tt, els, walls) => {
  const r1 = ITEMS[tt].w / 2 - 5;
  const hitEl = els.some(e => {
    if ((tt === 'sink' && e.type === 'window') || (tt === 'window' && e.type === 'sink')) return false;
    return Math.hypot(e.x - g.x, e.y - g.y) < r1 + ITEMS[e.type].w / 2 - 5;
  });
  let hitCab = false;
  // fridge, sink, stove all need base-cab clearance check
  if (['fridge', 'sink', 'stove', 'door'].includes(tt))
    hitCab = walls.some(w => ['base_cab', 'short'].includes(w.type) && checkOverlap(g.x, g.y, r1, w.x1, w.y1, w.x2, w.y2, 30 + r1));
  if (tt === 'window')
    hitCab = walls.some(w => w.type === 'upper_cab' && checkOverlap(g.x, g.y, r1, w.x1, w.y1, w.x2, w.y2, 15 + r1));
  return !hitEl && !hitCab;
};

// =============================================================================
// AUTO-FILL KITCHEN GENERATOR
// Reads the user's drawn walls, detects the shape, and places cabinets +
// appliances like a senior kitchen designer would.
// =============================================================================

// Seeded LCG RNG — same seed = same layout every time
function makeRng(seed) {
  let s = (seed ^ 0xdeadbeef) >>> 0;
  return () => { s = (Math.imul(1664525, s) + 1013904223) >>> 0; return s / 4294967296; };
}

// Return a unit normal vector that points INWARD to the room
// (picks the side facing the centroid of all walls)
function inwardNormal(wall, allWalls) {
  const dx = wall.x2 - wall.x1, dy = wall.y2 - wall.y1;
  const len = Math.hypot(dx, dy);
  const nx = -dy / len, ny = dx / len;
  // Centroid of all wall midpoints
  const cx = allWalls.reduce((s, w) => s + (w.x1 + w.x2) / 2, 0) / allWalls.length;
  const cy = allWalls.reduce((s, w) => s + (w.y1 + w.y2) / 2, 0) / allWalls.length;
  const mx = (wall.x1 + wall.x2) / 2, my = (wall.y1 + wall.y2) / 2;
  const dot = (cx - mx) * nx + (cy - my) * ny;
  return dot >= 0 ? { nx, ny } : { nx: -nx, ny: -ny };
}

// Place a point along a wall at fraction t (0=start, 1=end), offset inward by `offset`
function wallPoint(wall, t, nx, ny, offset) {
  return {
    x: wall.x1 + t * (wall.x2 - wall.x1) + nx * offset,
    y: wall.y1 + t * (wall.y2 - wall.y1) + ny * offset,
  };
}

// Rotation angle of a wall
function wallAngle(wall) {
  return Math.atan2(wall.y2 - wall.y1, wall.x2 - wall.x1);
}

// Distance between two {x,y} points
function dist2(a, b) { return Math.hypot(a.x - b.x, a.y - b.y); }

/**
 * Main auto-fill function.
 * Takes the user's existing solid walls and returns a new complete
 * { walls, elements } state with cabinets + appliances intelligently placed.
 */
function autoFillKitchen(userWalls, seed = Date.now()) {
  const rng = makeRng(seed);

  const solidWalls = userWalls.filter(w => w.type === 'solid');
  if (!solidWalls.length) return null;

  // ── Constants ────────────────────────────────────────────────────
  const BASE_INSET   = WALL_T / 2 + 30;   // from wall centerline → base cab center
  const UPPER_INSET  = WALL_T / 2 + 15;   // from wall centerline → upper cab center
  const CORNER_THRESH = 25;                // px — endpoints closer than this are "connected"
  const CORNER_GAP   = 35;                // cab setback from a CONNECTED corner end
  const FREE_GAP     = 5;                 // minimal setback from a FREE end
  const MIN_RUN      = 80;                // minimum usable wall length
  const APP_PAD      = 15;               // extra padding each side of an appliance cutout

  // ── Step 1: Detect which wall endpoints are "free" (not connected) ─
  // A connected endpoint is shared (within CORNER_THRESH) with another wall's endpoint.
  // The fridge MUST go at a free end — never at a corner junction.
  const endpts = solidWalls.flatMap(w => [
    { wid: w.id, end: 1, x: w.x1, y: w.y1 },
    { wid: w.id, end: 2, x: w.x2, y: w.y2 },
  ]);

  // freeEnds[wallId] = array of ends (1 and/or 2) that are unconnected
  const freeEnds = {};
  solidWalls.forEach(w => {
    freeEnds[w.id] = [1, 2].filter(end => {
      const ex = end === 1 ? w.x1 : w.x2;
      const ey = end === 1 ? w.y1 : w.y2;
      return !endpts.some(p => p.wid !== w.id && Math.hypot(p.x - ex, p.y - ey) < CORNER_THRESH);
    });
  });

  // ── Step 2: Compute geometry per wall ────────────────────────────
  const wallGeo = solidWalls
    .filter(w => Math.hypot(w.x2 - w.x1, w.y2 - w.y1) >= MIN_RUN)
    .map(w => {
      const len = Math.hypot(w.x2 - w.x1, w.y2 - w.y1);
      const { nx, ny } = inwardNormal(w, solidWalls);
      const ang        = wallAngle(w);
      const fe         = freeEnds[w.id];
      // Cabinet run starts/ends: CORNER_GAP at connected ends, FREE_GAP at free ends
      const tStart = (fe.includes(1) ? FREE_GAP   : CORNER_GAP) / len;
      const tEnd   = (fe.includes(2) ? FREE_GAP   : CORNER_GAP) / len;
      return { w, len, nx, ny, ang, fe,
        tS: Math.max(0, tStart),
        tE: Math.min(1, 1 - tEnd) };
    })
    .filter(g => g.tE > g.tS + 0.01);

  if (!wallGeo.length) return { walls: [...userWalls], elements: [] };

  // Sort longest first
  wallGeo.sort((a, b) => b.len - a.len);

  // ── Step 3: Assign roles ─────────────────────────────────────────
  // SINK: always longest wall (natural light convention — unchangeable)
  const sinkGeo = wallGeo[0];

  // FRIDGE: must be at a free end of some wall.
  //   Priority: different wall from sink → same wall last resort
  const fridgeCandidates = wallGeo
    .filter(g => g.fe.length > 0)               // must have a free end
    .sort((a, b) => {
      // Prefer different wall from sink
      const aScore = a.w.id !== sinkGeo.w.id ? 1 : 0;
      const bScore = b.w.id !== sinkGeo.w.id ? 1 : 0;
      return bScore - aScore;                    // higher score first
    });

  let fridgeGeo, fridgeEndNum;
  if (fridgeCandidates.length > 0) {
    // Pick from best candidates (same preference score), random among ties
    const best = fridgeCandidates[0];
    const ties = fridgeCandidates.filter(g => (g.w.id !== sinkGeo.w.id) === (best.w.id !== sinkGeo.w.id));
    fridgeGeo = ties[Math.floor(rng() * ties.length)];
    const fe  = fridgeGeo.fe;
    fridgeEndNum = fe[Math.floor(rng() * fe.length)]; // pick random free end
  } else {
    // All walls are fully connected (closed box) — fall back to end of longest non-sink wall
    fridgeGeo    = wallGeo.find(g => g.w.id !== sinkGeo.w.id) ?? wallGeo[1] ?? sinkGeo;
    fridgeEndNum = rng() > 0.5 ? 2 : 1;
  }

  // STOVE: prefer a fresh wall (not sink, not fridge)
  const stovePool = wallGeo.filter(g => g.w.id !== sinkGeo.w.id && g.w.id !== fridgeGeo.w.id);
  const stoveGeo  = stovePool.length > 0
    ? stovePool[Math.floor(rng() * stovePool.length)]
    : wallGeo.find(g => g.w.id !== fridgeGeo.w.id) ?? sinkGeo;

  // ── Step 4: Exact placement fractions ───────────────────────────
  // Helper: enforce minimum clear distance between two fracs on same wall
  const minSep = (typeA, typeB, wLen) =>
    (ITEMS[typeA].w / 2 + ITEMS[typeB].w / 2 + 25) / wLen; // 25cm clearance

  // Clamp frac away from a blocked zone [blockFrac ± blockHalf]
  const nudgeAway = (frac, blockFrac, blockHalf, tS, tE) => {
    const lo = blockFrac - blockHalf, hi = blockFrac + blockHalf;
    if (frac >= lo && frac <= hi) {
      // Push to whichever side has more room
      return (frac - tS) > (tE - frac) ? Math.min(tE, hi + blockHalf * 0.5) : Math.max(tS, lo - blockHalf * 0.5);
    }
    return frac;
  };

  // FRIDGE: snug at its free end
  const fridgeHalfFrac = (ITEMS.fridge.w / 2 + 5) / fridgeGeo.len;
  const fridgeFrac = fridgeEndNum === 1
    ? fridgeGeo.tS + fridgeHalfFrac
    : fridgeGeo.tE - fridgeHalfFrac;

  // SINK: 20%–80% of its run, but keep safe distance from fridge if same wall
  let sinkFrac = sinkGeo.tS + (0.2 + rng() * 0.6) * (sinkGeo.tE - sinkGeo.tS);
  if (sinkGeo.w.id === fridgeGeo.w.id) {
    const sep = minSep('sink', 'fridge', sinkGeo.len);
    sinkFrac = nudgeAway(sinkFrac, fridgeFrac, sep, sinkGeo.tS, sinkGeo.tE);
  }

  // STOVE: place by wall context, then enforce separation from sink and fridge
  let stoveFrac;
  if (stoveGeo.w.id === fridgeGeo.w.id) {
    stoveFrac = fridgeEndNum === 1
      ? stoveGeo.tS + (0.5 + rng() * 0.3) * (stoveGeo.tE - stoveGeo.tS)
      : stoveGeo.tS + (0.2 + rng() * 0.3) * (stoveGeo.tE - stoveGeo.tS);
  } else if (stoveGeo.w.id === sinkGeo.w.id) {
    const mid = (sinkGeo.tS + sinkGeo.tE) / 2;
    stoveFrac = sinkFrac < mid
      ? stoveGeo.tS + (0.6 + rng() * 0.25) * (stoveGeo.tE - stoveGeo.tS)
      : stoveGeo.tS + (0.15 + rng() * 0.25) * (stoveGeo.tE - stoveGeo.tS);
  } else {
    stoveFrac = stoveGeo.tS + (0.2 + rng() * 0.6) * (stoveGeo.tE - stoveGeo.tS);
  }
  // Enforce stove clearance from sink (same wall)
  if (stoveGeo.w.id === sinkGeo.w.id) {
    const sep = minSep('stove', 'sink', stoveGeo.len);
    stoveFrac = nudgeAway(stoveFrac, sinkFrac, sep, stoveGeo.tS, stoveGeo.tE);
  }
  // Enforce stove clearance from fridge (same wall)
  if (stoveGeo.w.id === fridgeGeo.w.id) {
    const sep = minSep('stove', 'fridge', stoveGeo.len);
    stoveFrac = nudgeAway(stoveFrac, fridgeFrac, sep, stoveGeo.tS, stoveGeo.tE);
  }

  // ── Step 5: Create appliance + window elements ───────────────────
  const elements = [];
  const makeAppl = (geo, frac, type) => {
    const pos = wallPoint(geo.w, frac, geo.nx, geo.ny, BASE_INSET);
    // Match the manual ghost rotation: atan2(inward_normal) - π/2
    // This puts the appliance back against the wall, face into the room
    const rot = Math.atan2(geo.ny, geo.nx) - Math.PI / 2;
    return { id: uid(), type, x: pos.x, y: pos.y, rotation: rot, swing: 1, scaleW: 1 };
  };

  const sinkEl   = makeAppl(sinkGeo,   sinkFrac,   'sink');
  const stoveEl  = makeAppl(stoveGeo,  stoveFrac,  'stove');
  const fridgeEl = makeAppl(fridgeGeo, fridgeFrac, 'fridge');
  elements.push(sinkEl, stoveEl, fridgeEl);

  // Window: on the actual solid wall surface at the sink position
  elements.push({
    id: uid(), type: 'window',
    x: sinkGeo.w.x1 + sinkFrac * (sinkGeo.w.x2 - sinkGeo.w.x1),
    y: sinkGeo.w.y1 + sinkFrac * (sinkGeo.w.y2 - sinkGeo.w.y1),
    rotation: sinkGeo.ang, swing: 1, scaleW: 0.9,
  });

  // ── Step 6: Cabinet gap maps ─────────────────────────────────────
  // Gaps are stored as [fracStart, fracEnd] on each wall
  const baseGaps  = {}; // cut at all appliances
  const upperGaps = {}; // cut at window + fridge only

  const addGap = (map, wallId, frac, halfPx, wallLen) => {
    const hf = (halfPx + APP_PAD) / wallLen;
    (map[wallId] ??= []).push([frac - hf, frac + hf]);
  };

  // Sink: exact-width cutout only — counter is flush against sink on both sides
  const sinkHf = (ITEMS.sink.w / 2) / sinkGeo.len;
  (baseGaps[sinkGeo.w.id] ??= []).push([sinkFrac - sinkHf, sinkFrac + sinkHf]);

  addGap(baseGaps,  stoveGeo.w.id,  stoveFrac,  ITEMS.stove.w  / 2, stoveGeo.len);  // stove drops into counter
  addGap(baseGaps,  fridgeGeo.w.id, fridgeFrac, ITEMS.fridge.w / 2, fridgeGeo.len); // fridge is standalone
  addGap(upperGaps, sinkGeo.w.id,   sinkFrac,   ITEMS.window.w * 0.9 / 2, sinkGeo.len);
  addGap(upperGaps, fridgeGeo.w.id, fridgeFrac, ITEMS.fridge.w / 2, fridgeGeo.len);

  // ── Step 7: Emit cabinet wall segments ───────────────────────────
  const subtractGaps = (tS, tE, gaps) => {
    const g = (gaps ?? [])
      .map(([a, b]) => [Math.max(tS, a), Math.min(tE, b)])
      .filter(([a, b]) => a < b)
      .sort((a, b) => a[0] - b[0]);
    const segs = []; let cur = tS;
    for (const [a, b] of g) {
      if (a > cur + 0.001) segs.push([cur, a]);
      cur = Math.max(cur, b);
    }
    if (cur < tE - 0.001) segs.push([cur, tE]);
    return segs;
  };

  const newWalls = [...userWalls];

  wallGeo.forEach(geo => {
    const wid = geo.w.id;
    const pushSeg = (type, inset, t1, t2) => {
      if ((t2 - t1) * geo.len < 30) return; // skip tiny scraps < 30cm
      const p1 = wallPoint(geo.w, t1, geo.nx, geo.ny, inset);
      const p2 = wallPoint(geo.w, t2, geo.nx, geo.ny, inset);
      newWalls.push({ id: uid(), type, x1: p1.x, y1: p1.y, x2: p2.x, y2: p2.y });
    };

    subtractGaps(geo.tS, geo.tE, baseGaps[wid])
      .forEach(([t1, t2]) => pushSeg('base_cab',  BASE_INSET,  t1, t2));
    subtractGaps(geo.tS, geo.tE, upperGaps[wid])
      .forEach(([t1, t2]) => pushSeg('upper_cab', UPPER_INSET, t1, t2));
  });

  return { walls: newWalls, elements };
}


// =============================================================================
// 3D SPRITE HELPER
// =============================================================================
const make3DSprite = (T, text, fg = '#fff', sz = 20, bg = 'rgba(15,23,42,0.8)') => {
  const dpr = Math.min(window.devicePixelRatio ?? 1, 2); // render at 2× for sharpness
  const c = document.createElement('canvas'), ctx = c.getContext('2d');
  ctx.font = `Bold ${sz}px Arial`;  // measure at 1× first
  const textW = ctx.measureText(text).width;
  c.width  = (textW + 30) * dpr;
  c.height = (sz   + 30) * dpr;
  ctx.scale(dpr, dpr);             // draw at 2×
  ctx.fillStyle = bg;
  if (ctx.roundRect) { ctx.beginPath(); ctx.roundRect(0, 0, textW + 30, sz + 30, 8); ctx.fill(); }
  else ctx.fillRect(0, 0, textW + 30, sz + 30);
  ctx.font = `Bold ${sz}px Arial`; ctx.fillStyle = fg;
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText(text, (textW + 30) / 2, (sz + 30) / 2);
  const s = new T.Sprite(new T.SpriteMaterial({ map: new T.CanvasTexture(c), depthTest: false }));
  // Keep display size same as before (compensate for 2× canvas)
  s.scale.set((textW + 30) * 0.4, (sz + 30) * 0.4, 1);
  return s;
};

// =============================================================================
// MAIN APP
// =============================================================================
export default function App() {
  const [st, dispatch] = useReducer(reducer, INIT);
  const { walls, elements, sel, past, future } = st;

  const [mode, setMode] = useState('2d');
  const [wideAngle, setWideAngle] = useState(false);
  const [tool, setTool] = useState('select');
  const [drawing, setDrawing] = useState(false);
  const [drawStart, setDrawStart] = useState({ x: 0, y: 0 });
  const [drawEnd, setDrawEnd] = useState({ x: 0, y: 0 });
  const [rawMouse, setRawMouse] = useState({ x: 0, y: 0 });
  const [ghost, setGhost] = useState(null);
  const [spaceDown, setSpaceDown] = useState(false);
  const [collapsed, setCollapsed] = useState(false);
  const [tooltip, setTooltip] = useState(null);
  const [saveMsg, setSaveMsg] = useState(false);
  const [, setDragTick] = useState(0);
  const [elWidths, setElWidths] = useState({});
  const [threeReady, setThreeReady] = useState(0);
  const [lastAutoSeed, setLastAutoSeed] = useState(null);  // null = never auto-filled
  const [autoMsg, setAutoMsg] = useState('');               // brief toast text
  const [doneState, setDoneState] = useState('idle');       // 'idle'|'switching'|'uploading'|'error'
  const pendingDoneRef = useRef(false);
  const performDoneRef = useRef(null);

  const [view, setView] = useState({ x: 0, y: 0, s: 1 });
  const viewRef = useRef(view);
  viewRef.current = view;
  const panRef = useRef({ active: false, sx: 0, sy: 0, vx: 0, vy: 0 });

  // Drag ref — stores visual offset, commits ONCE on pointerUp
  // { kind, id, sx, sy, ox, oy, [ox1,oy1,ox2,oy2 for walls], dx, dy, committed }
  const dragRef = useRef(null);

  const wallsRef = useRef(walls); wallsRef.current = walls;
  const elemsRef = useRef(elements); elemsRef.current = elements;
  const selRef = useRef(sel); selRef.current = sel;

  const svgRef = useRef(null);
  const threeMount = useRef(null);
  const ts = useRef({ mounted: false, scene: null, renderer: null, group: null, animId: null, wallMeshes: [] });
  const fileRef = useRef(null);

  // ── Responsive ───────────────────────────────────────────────────
  useEffect(() => { if (window.innerWidth < 768) setCollapsed(true); }, []);

  // ── Warnings (derived, not state) ────────────────────────────────
  const warnings = [];
  const solidWalls = walls.filter(w => w.type === 'solid');
  elements.forEach(el => {
    if (el.type === 'fridge') {
      // Find mount wall (closest)
      let mountDist = Infinity, mountId = null;
      solidWalls.forEach(w => {
        const d = ptSeg(el.x, el.y, w.x1, w.y1, w.x2, w.y2).dist;
        if (d < mountDist) { mountDist = d; mountId = w.id; }
      });
      // Only warn about OTHER walls being too close
      solidWalls.forEach(w => {
        if (w.id === mountId) return;
        const d = ptSeg(el.x, el.y, w.x1, w.y1, w.x2, w.y2).dist;
        if (d > 10 && d < 90)
          warnings.push({ x: el.x, y: el.y, msg: 'Fridge clearance < 90cm' });
      });
    }
    if (el.type === 'door') {
      elements.forEach(el2 => {
        if (el2.id > el.id && el2.type === 'door' && Math.hypot(el.x - el2.x, el.y - el2.y) < 130)
          warnings.push({ x: (el.x + el2.x) / 2, y: (el.y + el2.y) / 2, msg: 'Doors overlap' });
      });
    }
  });

  // ── Coordinate conversion ────────────────────────────────────────
  // Returns raw world coords and grid-snapped world coords
  const toWorld = useCallback((cx, cy) => {
    if (!svgRef.current) return { x: 0, y: 0, rx: 0, ry: 0 };
    const r = svgRef.current.getBoundingClientRect();
    const v = viewRef.current;
    const rx = (cx - r.left - v.x) / v.s;
    const ry = (cy - r.top - v.y) / v.s;
    return { x: gridSnap(rx), y: gridSnap(ry), rx, ry };
  }, []);

  // ── Endpoint snap — ONLY for wall tools, never cabinets ──────────
  // threshold is in SCREEN pixels, converted to world units at current zoom
  const findEndpointSnap = useCallback((rx, ry) => {
    const worldThreshold = ENDPOINT_SNAP_PX / viewRef.current.s;
    let best = null, bd = worldThreshold;
    wallsRef.current.forEach(w => {
      for (const [px, py] of [[w.x1, w.y1], [w.x2, w.y2]]) {
        const d = Math.hypot(rx - px, ry - py);
        if (d < bd) { bd = d; best = { x: px, y: py }; }
      }
    });
    return best;
  }, []);

  // ── Hit testing ──────────────────────────────────────────────────
  const hitEl = useCallback((rx, ry) => {
    for (let i = elemsRef.current.length - 1; i >= 0; i--) {
      const el = elemsRef.current[i], c = ITEMS[el.type];
      if (!c) continue;
      const cs = Math.cos(-el.rotation), sn = Math.sin(-el.rotation);
      const lx = cs * (rx - el.x) - sn * (ry - el.y);
      const ly = sn * (rx - el.x) + cs * (ry - el.y);
      if (Math.abs(lx) <= c.w / 2 + 8 && Math.abs(ly) <= c.d / 2 + 8) return el;
    }
    return null;
  }, []);

  const hitWall = useCallback((rx, ry) => {
    for (let i = wallsRef.current.length - 1; i >= 0; i--) {
      const w = wallsRef.current[i];
      if (ptSeg(rx, ry, w.x1, w.y1, w.x2, w.y2).dist < wallThick(w.type) / 2 + 8) return w;
    }
    return null;
  }, []);

  // ── Ghost element — ALWAYS visible, wall-snap is magnetic assist ─
  const computeGhost = useCallback((rx, ry) => {
    const it = ITEMS[tool];
    if (!it) return null;

    // Default: ghost follows cursor freely (grid-snapped for clean placement)
    let tx = gridSnap(rx), ty = gridSnap(ry), rot = 0;
    let snapped = false;

    // Wall-mount magnetic assist — only activates when cursor is close to a wall
    const mountWalls = wallsRef.current.filter(w => w.type === 'solid' || w.type === 'short');
    let nearWall = null, nearDist = Infinity, nearPt = null;

    for (const w of mountWalls) {
      const pt = ptSeg(rx, ry, w.x1, w.y1, w.x2, w.y2);
      // Clamp along wall so element stays within wall bounds
      const wl = Math.hypot(w.x2 - w.x1, w.y2 - w.y1), hw = it.w / 2;
      if (wl >= it.w) {
        const tC = Math.max(hw / wl, Math.min(1 - hw / wl, pt.t));
        pt.x = w.x1 + tC * (w.x2 - w.x1); pt.y = w.y1 + tC * (w.y2 - w.y1);
      } else {
        pt.x = (w.x1 + w.x2) / 2; pt.y = (w.y1 + w.y2) / 2;
      }
      pt.dist = Math.hypot(rx - pt.x, ry - pt.y);

      if (pt.dist < MOUNT_MAGNET && pt.dist < nearDist) {
        nearDist = pt.dist; nearWall = w; nearPt = pt;
      }
    }

    if (nearWall) {
      snapped = true;
      const wa = Math.atan2(nearWall.y2 - nearWall.y1, nearWall.x2 - nearWall.x1);

      if (it.mount === 'against') {
        const dx = nearWall.x2 - nearWall.x1, dy = nearWall.y2 - nearWall.y1;
        const l = Math.hypot(dx, dy);
        const n1x = -dy / l, n1y = dx / l;
        const d1 = (rx - nearPt.x) * n1x + (ry - nearPt.y) * n1y;
        const bx = d1 >= 0 ? n1x : -n1x, by = d1 >= 0 ? n1y : -n1y;
        rot = Math.atan2(by, bx) - Math.PI / 2;
        const wt = nearWall.type === 'short' ? 60 : WALL_T;
        tx = nearPt.x + bx * (it.d / 2 + wt / 2);
        ty = nearPt.y + by * (it.d / 2 + wt / 2);
      } else {
        // Inside wall (door, window)
        tx = nearPt.x; ty = nearPt.y; rot = wa;
      }
    }

    return { x: tx, y: ty, rotation: rot, snapped };
  }, [tool]);

  // ── POINTER DOWN ─────────────────────────────────────────────────
  const onDown = useCallback(e => {
    if (mode !== '2d') return;
    const { x, y, rx, ry } = toWorld(e.clientX, e.clientY);

    // Pan: middle-click or space
    if (e.button === 1 || spaceDown) {
      e.preventDefault();
      panRef.current = { active: true, sx: e.clientX, sy: e.clientY, vx: viewRef.current.x, vy: viewRef.current.y };
      return;
    }

    // ── SELECT TOOL ────────────────────────────
    if (tool === 'select') {
      const el = hitEl(rx, ry);
      if (el) {
        dispatch({ type: 'SEL', p: { type: 'element', id: el.id } });
        dragRef.current = { kind: 'el', id: el.id, sx: rx, sy: ry, ox: el.x, oy: el.y, dx: 0, dy: 0, moved: false };
        return;
      }
      
      // Node (endpoint) dragging for selected wall/cabinet
      // Read sel from ref — NOT from closure (useCallback doesn't track sel)
      const curSel = selRef.current;
      if (curSel?.type === 'wall') {
        const sw = wallsRef.current.find(w => w.id === curSel.id);
        const nodeHitR = 24 / viewRef.current.s;  // 24 screen pixels
        if (sw) {
          if (Math.hypot(rx - sw.x1, ry - sw.y1) < nodeHitR) {
            dragRef.current = { kind: 'node', id: sw.id, node: 1, sx: rx, sy: ry, px: sw.x1, py: sw.y1, moved: false };
            return;
          }
          if (Math.hypot(rx - sw.x2, ry - sw.y2) < nodeHitR) {
            dragRef.current = { kind: 'node', id: sw.id, node: 2, sx: rx, sy: ry, px: sw.x2, py: sw.y2, moved: false };
            return;
          }
        }
      }

      const w = hitWall(rx, ry);
      if (w) {
        dispatch({ type: 'SEL', p: { type: 'wall', id: w.id } });
        dragRef.current = { kind: 'wall', id: w.id, sx: rx, sy: ry, ox1: w.x1, oy1: w.y1, ox2: w.x2, oy2: w.y2, dx: 0, dy: 0, moved: false };
        return;
      }
      dispatch({ type: 'DESEL' });
      return;
    }

    // ── DRAW TOOLS ─────────────────────────────
    if (DRAW_TOOLS.includes(tool)) {
      // Endpoint snap only for wall tools
      let sx = x, sy = y;
      if (ENDPOINT_SNAP_TOOLS.includes(tool)) {
        const sp = findEndpointSnap(rx, ry);
        if (sp) { sx = sp.x; sy = sp.y; }
      }
      setDrawing(true); setDrawStart({ x: sx, y: sy }); setDrawEnd({ x: sx, y: sy }); setRawMouse({ x: rx, y: ry });
      return;
    }

    // ── ELEMENT PLACEMENT ──────────────────────
    if (ITEMS[tool] && ghost) {
      if (validateGhost(ghost, tool, elemsRef.current, wallsRef.current)) {
        const scaleW = elWidths[tool] ?? 1;
        dispatch({ type: 'ADD_EL', p: { id: uid(), type: tool, x: ghost.x, y: ghost.y, rotation: ghost.rotation, swing: 1, scaleW } });
      }
    }
  }, [mode, tool, spaceDown, toWorld, hitEl, hitWall, findEndpointSnap, ghost, elWidths]);

  // ── POINTER MOVE ─────────────────────────────────────────────────
  const onMove = useCallback(e => {
    if (mode !== '2d') return;
    const { x, y, rx, ry } = toWorld(e.clientX, e.clientY);
    setRawMouse({ x: rx, y: ry });

    // ── PAN ────────────────────────────────────
    if (panRef.current.active) {
      const p = panRef.current;
      setView(v => ({ ...v, x: p.vx + (e.clientX - p.sx), y: p.vy + (e.clientY - p.sy) }));
      return;
    }

    // ── DRAG (free movement, NO grid snap) ─────
    if (dragRef.current && e.buttons === 1) {
      const d = dragRef.current;
      d.dx = rx - d.sx;
      d.dy = ry - d.sy;
      if (Math.abs(d.dx) > 3 || Math.abs(d.dy) > 3) d.moved = true;
      
      // Node (endpoint) resizing logic
      if (d.kind === 'node') {
        let cx = rx, cy = ry;

        // Cabins: freeform — no grid snap, no endpoint snap
        const nodeWall = wallsRef.current.find(w => w.id === d.id);
        const isCabin = nodeWall?.type === 'base_cab' || nodeWall?.type === 'upper_cab';

        if (!isCabin) {
          // Walls: endpoint snap first (magnetize to other nodes)
          let snapped = false;
          const sp = findEndpointSnap(rx, ry);
          if (sp) { cx = sp.x; cy = sp.y; snapped = true; }

          if (!snapped) {
            cx = gridSnap(rx); cy = gridSnap(ry);
            if (e.shiftKey) { // Axis lock
               if (nodeWall) {
                 const ox = d.node === 1 ? nodeWall.x2 : nodeWall.x1;
                 const oy = d.node === 1 ? nodeWall.y2 : nodeWall.y1;
                 if (Math.abs(cx - ox) > Math.abs(cy - oy)) cy = oy; else cx = ox;
               }
            }
          }
        }
        // else: cabin — cx/cy stay as raw rx, ry (no snap)

        d.px = cx; d.py = cy;
      }

      // Trigger re-render to show drag preview
      setDragTick(t => t + 1);
      return;
    }

    // ── DRAWING ────────────────────────────────
    if (drawing) {
      let cx = x, cy = y;

      // 1. Apply endpoint snap first (walls only) — snap beats axis-lock
      //    because a snapped endpoint is an exact match, not an approximation.
      let snapped = false;
      if (ENDPOINT_SNAP_TOOLS.includes(tool)) {
        const sp = findEndpointSnap(rx, ry);
        if (sp) { cx = sp.x; cy = sp.y; snapped = true; }
      }

      // 2. Axis-lock with shift — only when NOT snapped to an endpoint
      if (!snapped && e.shiftKey) {
        if (Math.abs(rx - drawStart.x) > Math.abs(ry - drawStart.y)) cy = drawStart.y;
        else cx = drawStart.x;
      }

      setDrawEnd({ x: cx, y: cy });
      return;
    }

    // ── GHOST ELEMENT (always visible) ─────────
    if (ITEMS[tool]) {
      setGhost(computeGhost(rx, ry));
    } else {
      setGhost(null);
    }
  }, [mode, toWorld, drawing, drawStart, findEndpointSnap, tool, computeGhost]);

  // ── POINTER UP ───────────────────────────────────────────────────
  const onUp = useCallback(() => {
    if (mode !== '2d') return;
    panRef.current.active = false;

    // ── COMMIT DRAG (single history entry) ─────
    if (dragRef.current?.moved) {
      const d = dragRef.current;
      if (d.kind === 'el') {
        // Free position — no grid snap on drag
        dispatch({ type: 'UPD_EL', p: { id: d.id, x: d.ox + d.dx, y: d.oy + d.dy } });
      } else if (d.kind === 'wall') {
        dispatch({
          type: 'UPD_WALL', p: {
            id: d.id,
            x1: d.ox1 + d.dx, y1: d.oy1 + d.dy,
            x2: d.ox2 + d.dx, y2: d.oy2 + d.dy
          }
        });
      } else if (d.kind === 'node') {
        const sw = wallsRef.current.find(w => w.id === d.id);
        if (sw) {
          if (d.node === 1) dispatch({ type: 'UPD_WALL', p: { id: d.id, x1: d.px, y1: d.py, x2: sw.x2, y2: sw.y2 } });
          else dispatch({ type: 'UPD_WALL', p: { id: d.id, x1: sw.x1, y1: sw.y1, x2: d.px, y2: d.py } });
        }
      }
    }
    dragRef.current = null;

    // ── COMMIT DRAWING ─────────────────────────
    if (drawing) {
      if (drawStart.x !== drawEnd.x || drawStart.y !== drawEnd.y) {
        if (validateLine(drawStart, drawEnd, tool, elemsRef.current)) {
          let wt = 'solid', fx1 = drawStart.x, fy1 = drawStart.y, fx2 = drawEnd.x, fy2 = drawEnd.y;
          if (tool === 'virtual_wall') wt = 'virtual';
          else if (tool === 'short_wall') wt = 'short';
          else if (tool === 'base_cab' || tool === 'upper_cab') {
            wt = tool;
            const depth = tool === 'base_cab' ? 60 : 30;
            const off = dynOffset(drawStart.x, drawStart.y, drawEnd.x, drawEnd.y, rawMouse.x, rawMouse.y, depth);
            const tracing = wallsRef.current.some(w => ['solid', 'short'].includes(w.type) &&
              ptSeg(drawStart.x, drawStart.y, w.x1, w.y1, w.x2, w.y2).dist < 15 &&
              ptSeg(drawEnd.x, drawEnd.y, w.x1, w.y1, w.x2, w.y2).dist < 15);
            if (tracing) { fx1 += off.sx; fy1 += off.sy; fx2 += off.sx; fy2 += off.sy; }
          }
          dispatch({ type: 'ADD_WALL', p: { id: uid(), x1: fx1, y1: fy1, x2: fx2, y2: fy2, type: wt } });
        }
      }
      setDrawing(false);
    }
  }, [mode, drawing, drawStart, drawEnd, tool, rawMouse]);

  // ── Wheel zoom ───────────────────────────────────────────────────
  useEffect(() => {
    const el = svgRef.current; if (!el) return;
    const handler = e => {
      e.preventDefault();
      const r = el.getBoundingClientRect();
      const mx = e.clientX - r.left, my = e.clientY - r.top;
      setView(v => {
        const f = e.deltaY > 0 ? 0.92 : 1.08;
        const ns = Math.max(0.1, Math.min(8, v.s * f));
        return { x: mx - (mx - v.x) * (ns / v.s), y: my - (my - v.y) * (ns / v.s), s: ns };
      });
    };
    el.addEventListener('wheel', handler, { passive: false });
    return () => el.removeEventListener('wheel', handler);
  }, []);

  const zoomBtn = dir => setView(v => ({ ...v, s: Math.max(0.1, Math.min(8, v.s * (dir > 0 ? 1.25 : 0.8))) }));

  const fitView = () => {
    if (!svgRef.current) return;
    const pts = [...walls.flatMap(w => [{ x: w.x1, y: w.y1 }, { x: w.x2, y: w.y2 }]), ...elements.map(e => ({ x: e.x, y: e.y }))];
    if (!pts.length) { setView({ x: 0, y: 0, s: 1 }); return; }
    const pad = 80;
    const mnx = Math.min(...pts.map(p => p.x)), mny = Math.min(...pts.map(p => p.y));
    const mxx = Math.max(...pts.map(p => p.x)), mxy = Math.max(...pts.map(p => p.y));
    const r = svgRef.current.getBoundingClientRect();
    const bw = mxx - mnx + pad * 2, bh = mxy - mny + pad * 2;
    const s = Math.min(r.width / bw, r.height / bh, 3);
    setView({ x: (r.width - bw * s) / 2 - (mnx - pad) * s, y: (r.height - bh * s) / 2 - (mny - pad) * s, s });
  };

  // ── Keyboard ─────────────────────────────────────────────────────
  useEffect(() => {
    const down = e => {
      const tag = document.activeElement?.tagName;
      const inputType = document.activeElement?.type;
      // Only block hotkeys for text-like inputs, not range sliders or buttons
      if ((tag === 'INPUT' && inputType !== 'range') || tag === 'TEXTAREA') return;
      if (e.code === 'Space') { e.preventDefault(); setSpaceDown(true); return; }
      if (e.key === 'Escape') { setDrawing(false); dispatch({ type: 'DESEL' }); return; }
      if ((e.key === 'Delete' || e.key === 'Backspace') && sel) {
        e.preventDefault();
        dispatch({ type: sel.type === 'wall' ? 'DEL_WALL' : 'DEL_EL', p: sel.id });
        return;
      }
      const mac = navigator.platform.toUpperCase().includes('MAC');
      const ctrl = mac ? e.metaKey : e.ctrlKey;
      
      // Duplicate
      if (ctrl && e.key.toLowerCase() === 'd' && sel) {
        e.preventDefault();
        const nid = uid();
        if (sel.type === 'element') {
          const el = elemsRef.current.find(o => o.id === sel.id);
          if (el) {
            dispatch({ type: 'ADD_EL', p: { ...el, id: nid, x: el.x + 20, y: el.y + 20 } });
            dispatch({ type: 'SEL', p: { type: 'element', id: nid } });
          }
        } else if (sel.type === 'wall') {
          const w = wallsRef.current.find(o => o.id === sel.id);
          if (w) {
            dispatch({ type: 'ADD_WALL', p: { ...w, id: nid, x1: w.x1 + 20, y1: w.y1 + 20, x2: w.x2 + 20, y2: w.y2 + 20 } });
            dispatch({ type: 'SEL', p: { type: 'wall', id: nid } });
          }
        }
        return;
      }

      if (ctrl && e.shiftKey && e.key.toLowerCase() === 'z') { e.preventDefault(); dispatch({ type: 'REDO' }); return; }
      if (ctrl && e.key.toLowerCase() === 'z') { e.preventDefault(); dispatch({ type: 'UNDO' }); return; }
      if (!ctrl) { const td = TOOL_DEFS.find(t => t.sc === e.key.toUpperCase()); if (td) setTool(td.key); }
    };
    const up = e => { if (e.code === 'Space') setSpaceDown(false); };
    window.addEventListener('keydown', down); window.addEventListener('keyup', up);
    return () => { window.removeEventListener('keydown', down); window.removeEventListener('keyup', up); };
  }, [sel]);

  // ── Export/Import ────────────────────────────────────────────────
  // ── Auto-fill + Shuffle ──────────────────────────────────────────
  const handleAutoFill = (seed = Date.now()) => {
    const solidCount = wallsRef.current.filter(w => w.type === 'solid').length;
    if (!solidCount) {
      setAutoMsg('Draw at least 1 wall first!');
      setTimeout(() => setAutoMsg(''), 2500);
      return;
    }
    // Keep only the user's drawn walls (strip any prior auto-cab runs)
    const userWalls = wallsRef.current.filter(w =>
      w.type === 'solid' || w.type === 'virtual' || w.type === 'short'
    );
    const result = autoFillKitchen(userWalls, seed);
    if (!result) return;
    dispatch({ type: 'LOAD', p: result });
    setLastAutoSeed(seed);
    const shape = solidCount === 1 ? 'Single Wall' : solidCount === 2 ? 'L-Shape' : 'U-Shape';
    setAutoMsg(`✨ ${shape} generated!`);
    setTimeout(() => setAutoMsg(''), 2500);
  };

  const handleShuffle = () => {
    const userWalls = wallsRef.current.filter(w =>
      w.type === 'solid' || w.type === 'virtual' || w.type === 'short'
    );
    const newSeed = Date.now();
    const result = autoFillKitchen(userWalls, newSeed);
    if (!result) return;
    dispatch({ type: 'LOAD', p: result });
    setLastAutoSeed(newSeed);
    setAutoMsg('🔀 New arrangement!');
    setTimeout(() => setAutoMsg(''), 2000);
  };

  const exportJSON = () => {

    const blob = new Blob([JSON.stringify({ walls, elements }, null, 2)], { type: 'application/json' });
    const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = 'kitchsketch.json'; a.click();
    URL.revokeObjectURL(a.href); setSaveMsg(true); setTimeout(() => setSaveMsg(false), 2000);
  };
  const importJSON = e => {
    const f = e.target.files?.[0]; if (!f) return;
    const r = new FileReader();
    r.onload = ev => { try { dispatch({ type: 'LOAD', p: JSON.parse(ev.target.result) }); } catch { alert('Invalid file'); } };
    r.readAsText(f); e.target.value = '';
  };
  const exportPNG = () => {
    if (mode === '3d') {
      // ── 3D export: re-render at current camera angle then grab canvas ──
      const s = ts.current;
      if (!s.renderer || !s.scene || !s.cam) return;
      s.renderer.render(s.scene, s.cam);          // force a fresh render
      const url = s.renderer.domElement.toDataURL('image/png');
      const a = document.createElement('a');
      a.href = url; a.download = 'kitchsketch-3d.png'; a.click();
      return;
    }
    // ── 2D export: SVG → canvas → PNG ────────────────────────────────
    if (!svgRef.current) return;
    const clone = svgRef.current.cloneNode(true);
    clone.setAttribute('xmlns', 'http://www.w3.org/2000/svg');
    const data = new XMLSerializer().serializeToString(clone);
    const blob = new Blob([data], { type: 'image/svg+xml;charset=utf-8' });
    const url = URL.createObjectURL(blob);
    const img = new Image();
    img.onload = () => {
      const c = document.createElement('canvas');
      c.width = svgRef.current.clientWidth * 2; c.height = svgRef.current.clientHeight * 2;
      const ctx = c.getContext('2d');
      ctx.fillStyle = '#0f0f0f'; ctx.fillRect(0, 0, c.width, c.height);
      ctx.drawImage(img, 0, 0, c.width, c.height);
      const a = document.createElement('a'); a.href = c.toDataURL('image/png'); a.download = 'kitchsketch.png'; a.click();
      URL.revokeObjectURL(url);
    };
    img.src = url;
  };

  // ── Done: 3D export → Supabase upload → redirect ─────────────────
  const performDone = async () => {
    const s = ts.current;
    if (!s.renderer || !s.scene || !s.cam) {
      setDoneState('error');
      setTimeout(() => setDoneState('idle'), 3000);
      return;
    }
    setDoneState('uploading');
    try {
      // Force a fresh render at current camera angle
      s.renderer.render(s.scene, s.cam);

      // Capture as JPEG blob (same format sketch.html used)
      const blob = await new Promise((resolve, reject) => {
        s.renderer.domElement.toBlob(
          b => (b ? resolve(b) : reject(new Error('Canvas capture failed'))),
          'image/jpeg',
          0.95,
        );
      });

      // Upload to Supabase bucket 'TREE'
      const sb = window.supabase?.createClient(
        'https://whmbrguzumyatnslzfsq.supabase.co',
        'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6IndobWJyZ3V6dW15YXRuc2x6ZnNxIiwicm9sZSI6InNlcnZpY2Vfcm9sZSIsImlhdCI6MTc0OTM1MTY4OSwiZXhwIjoyMDY0OTI3Njg5fQ.h-YbToBRx8WTW5KCk2IAYnmuhob3oiARGsnn61HwYQc',
      );
      if (!sb) throw new Error('Supabase SDK not loaded — check sketch.html CDN script');

      const fileName = `sketch_${Date.now()}.jpg`;
      const { error } = await sb.storage
        .from('TREE')
        .upload(fileName, blob, { contentType: 'image/jpeg', upsert: false });
      if (error) throw error;

      const { data: { publicUrl } } = sb.storage.from('TREE').getPublicUrl(fileName);

      // Fallback store + redirect (same flow as old sketch.html)
      localStorage.setItem('nanobanana_sketch_url', publicUrl);
      setTimeout(() => {
        window.location.href = `index.html?sketch_url=${encodeURIComponent(publicUrl)}`;
      }, 300);
    } catch (err) {
      console.error('Done export failed:', err);
      setDoneState('error');
      setTimeout(() => setDoneState('idle'), 3000);
    }
  };

  // Keep a stable ref so effects can call the latest version
  performDoneRef.current = performDone;

  const handleDone = () => {
    if (!walls.length && !elements.length) return; // nothing drawn
    if (mode !== '3d') {
      // Switch to 3D first; performDone fires once the scene is ready
      pendingDoneRef.current = true;
      setDoneState('switching');
      setMode('3d');
    } else if (ts.current.renderer) {
      performDone();
    } else {
      // Already in 3D mode but renderer not initialised yet
      pendingDoneRef.current = true;
      setDoneState('switching');
    }
  };

  // ── 3D INIT ──────────────────────────────────────────────────────
  useEffect(() => {
    if (mode !== '3d' || !threeMount.current) return;
    const s = ts.current; s.mounted = true;
    const init = () => {
      if (!s.mounted || !window.THREE) return;
      const T = window.THREE;
      const scene = new T.Scene(); scene.background = new T.Color('#f8fafc'); s.scene = scene;
      const mt = threeMount.current;
      const cam = new T.PerspectiveCamera(45, mt.clientWidth / mt.clientHeight, 1, 10000);
      let rad = 1200, ang = Math.PI / 4, pit = Math.PI / 6;
      const uc = () => { cam.position.set(rad * Math.cos(pit) * Math.cos(ang), rad * Math.sin(pit), rad * Math.cos(pit) * Math.sin(ang)); cam.lookAt(scene.position); };
      uc();
      const ren = new T.WebGLRenderer({ antialias: true, preserveDrawingBuffer: true });
      ren.setPixelRatio(Math.min(window.devicePixelRatio, 2)); // HiDPI / Retina
      ren.setSize(mt.clientWidth, mt.clientHeight); ren.shadowMap.enabled = true;
      ren.shadowMap.type = T.PCFSoftShadowMap; // softer shadows
      mt.innerHTML = ''; mt.appendChild(ren.domElement);
      s.renderer = ren; s.cam = cam; // store cam so exportPNG can re-render at current angle
      scene.add(new T.AmbientLight(0xffffff, 0.6));
      const dl = new T.DirectionalLight(0xffffff, 0.6); dl.position.set(200, 500, 300); dl.castShadow = true; scene.add(dl);
      const grid = new T.GridHelper(2000, 100); grid.position.y = 1; grid.material.opacity = 0.2; grid.material.transparent = true; scene.add(grid);
      const g = new T.Group(); scene.add(g); s.group = g;
      let dragging = false, prev = { x: 0, y: 0 };
      const cv = ren.domElement;
      const H = {
        mousedown: ev => { dragging = true; prev = { x: ev.clientX, y: ev.clientY }; },
        mouseup: () => dragging = false, mouseleave: () => dragging = false,
        mousemove: ev => { if (!dragging) return; ang += (ev.clientX - prev.x) * 0.01; pit = Math.max(0.05, Math.min(1.52, pit + (ev.clientY - prev.y) * 0.01)); uc(); prev = { x: ev.clientX, y: ev.clientY }; },
        wheel: ev => { ev.preventDefault(); rad = Math.max(300, Math.min(4000, rad + ev.deltaY * 0.5)); uc(); },
        touchstart: ev => { dragging = true; prev = { x: ev.touches[0].clientX, y: ev.touches[0].clientY }; },
        touchend: () => dragging = false,
        touchmove: ev => { ev.preventDefault(); ang += (ev.touches[0].clientX - prev.x) * 0.01; pit = Math.max(0.05, Math.min(1.52, pit + (ev.touches[0].clientY - prev.y) * 0.01)); uc(); prev = { x: ev.touches[0].clientX, y: ev.touches[0].clientY }; },
      };
      Object.entries(H).forEach(([e, fn]) => cv.addEventListener(e, fn, (e === 'wheel' || e === 'touchmove') ? { passive: false } : undefined));
      const animate = () => {
        if (!s.mounted) return; s.animId = requestAnimationFrame(animate);
        const cd = new T.Vector3(cam.position.x, 0, cam.position.z).normalize();
        s.wallMeshes.forEach(m => { 
          const wd = new T.Vector3(m.position.x, 0, m.position.z); 
          if (wd.lengthSq() < 1) return; 
          wd.normalize(); 
          // Only structural walls go transparent when blocking camera, cabinets stay solid
          m.material.opacity = (!m.userData.isCab && wd.dot(cd) > 0.5) ? 0.35 : 1.0; 
          m.material.depthWrite = m.material.opacity > 0.5; 
        });
        ren.render(scene, cam);
      };
      animate();
      return () => Object.entries(H).forEach(([e, fn]) => cv.removeEventListener(e, fn));
    };
    let cleanup;
    if (!window.THREE) {
      const sc = document.createElement('script');
      sc.src = 'https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js';
      sc.onload = () => {
        cleanup = init();
        // Force the content effect to re-run now that scene/group exist
        setThreeReady(r => r + 1);
      };
      document.head.appendChild(sc);
    } else { cleanup = init(); }
    return () => { s.mounted = false; if (s.animId) cancelAnimationFrame(s.animId); cleanup?.(); if (threeMount.current) threeMount.current.innerHTML = ''; s.scene = null; s.renderer = null; s.group = null; s.wallMeshes = []; };
  }, [mode]);

  // ── 3D CONTENT ───────────────────────────────────────────────────
  useEffect(() => {
    const s = ts.current;
    if (!s.group || !s.mounted || !window.THREE) return;
    const T = window.THREE, g = s.group;
    while (g.children.length) { const c = g.children[0]; c.traverse?.(o => { o.geometry?.dispose(); if (o.material) { if (Array.isArray(o.material)) o.material.forEach(m => m.dispose()); else o.material.dispose(); } }); g.remove(c); }
    s.wallMeshes = [];
    if (!walls.length && !elements.length) return;
    let mnx = Infinity, mny = Infinity, mxx = -Infinity, mxy = -Infinity;
    walls.forEach(w => { mnx = Math.min(mnx, w.x1, w.x2); mxx = Math.max(mxx, w.x1, w.x2); mny = Math.min(mny, w.y1, w.y2); mxy = Math.max(mxy, w.y1, w.y2); });
    if (!isFinite(mnx)) { mnx = 0; mxx = 400; mny = 0; mxy = 400; }
    const cx = (mnx + mxx) / 2, cy = (mny + mxy) / 2;
    if (walls.length) {
      const f = new T.Mesh(new T.PlaneGeometry(Math.max(100, mxx - mnx) + 80, Math.max(100, mxy - mny) + 80), new T.MeshLambertMaterial({ color: '#e1ceb1', side: T.DoubleSide }));
      f.rotation.x = Math.PI / 2; f.receiveShadow = true; g.add(f);
    }
    walls.forEach(w => {
      if (w.type === 'virtual') return;
      const len = Math.hypot(w.x2 - w.x1, w.y2 - w.y1), ang = Math.atan2(w.y2 - w.y1, w.x2 - w.x1);
      const px = (w.x1 + w.x2) / 2 - cx, py = (w.y1 + w.y2) / 2 - cy;
      let h = WALL_H, d = WALL_T, elev = 0, col = '#ffffff';
      if (w.type === 'short') { h = 100; d = 60; col = '#e2e8f0'; }
      else if (w.type === 'base_cab') { h = 90; d = 60; col = '#d97706'; }
      else if (w.type === 'upper_cab') { h = 80; d = 30; elev = 135; col = '#b45309'; }
      const m = new T.Mesh(new T.BoxGeometry(len, h, d), new T.MeshLambertMaterial({ color: col, transparent: true }));
      m.position.set(px, h / 2 + elev, py); m.rotation.y = -ang; m.castShadow = true; m.receiveShadow = true;
      m.userData.isCab = (w.type === 'base_cab' || w.type === 'upper_cab');
      g.add(m); s.wallMeshes.push(m);

      // ── Cabinet module dividers every 60 cm ────────────────────────
      if (w.type === 'base_cab' || w.type === 'upper_cab') {
        const MODULE = 60;
        const divCount = Math.floor(len / MODULE);
        const divMat = new T.MeshLambertMaterial({ color: w.type === 'base_cab' ? '#b45309' : '#92400e' });
        for (let i = 1; i < divCount; i++) {
          // offset from cabinet center: i * MODULE - len/2
          const localX = i * MODULE - len / 2;
          const div = new T.Mesh(new T.BoxGeometry(2, h, d + 1), divMat);
          div.position.set(px + Math.cos(ang) * localX, h / 2 + elev, py + Math.sin(ang) * localX);
          div.rotation.y = -ang;
          g.add(div);
        }
      }

      if (w.type === 'base_cab') {
        const slab = new T.Mesh(new T.BoxGeometry(len + 4, 3, d + 4), new T.MeshLambertMaterial({ color: '#78716c' }));
        slab.position.set(px, h + 1.5, py); slab.rotation.y = -ang; g.add(slab);
      }
      if (w.type === 'solid' || w.type === 'short') {
        const sp = make3DSprite(T, `${Math.round(len)} cm`, '#fff', 18, 'rgba(59,130,246,0.9)');
        sp.position.set(px, h + 20, py); g.add(sp);
      }
    });
    elements.forEach(el => {
      const c = ITEMS[el.type]; if (!c) return;
      // scaleW: per-element width multiplier (set at placement via size slider)
      const sw = el.scaleW ?? 1;
      const ew = c.w * sw;  // effective width
      const eg = new T.Group(); eg.position.set(el.x - cx, 0, el.y - cy); eg.rotation.y = -el.rotation;
      const addMesh = (geo, mat, px, py, pz) => {
        const m = new T.Mesh(geo, mat);
        m.position.set(px, py, pz);
        eg.add(m);
        return m;
      };
      if (el.type === 'sink') {
        // Cabinet body — same amber as base cabinets
        addMesh(new T.BoxGeometry(ew, c.h - 5, c.d), new T.MeshLambertMaterial({ color: '#d97706' }), 0, (c.h - 5) / 2, 0);
        // Countertop slab (stone grey)
        addMesh(new T.BoxGeometry(ew + 4, 4, c.d + 4), new T.MeshLambertMaterial({ color: '#94a3b8' }), 0, c.h - 2, 0);
        // Basin bowl — slightly inset, white porcelain
        const basinW = ew * 0.65, basinD = c.d * 0.65, basinH = 12;
        addMesh(new T.BoxGeometry(basinW, basinH, basinD), new T.MeshLambertMaterial({ color: '#f8fafc', side: T.DoubleSide }), 0, c.h - 2 - basinH / 2 + 1, 0);
        // Faucet neck (thin vertical bar)
        addMesh(new T.BoxGeometry(4, 28, 4), new T.MeshLambertMaterial({ color: '#cbd5e1' }), 0, c.h + 12, -c.d * 0.2);
        // Faucet spout (horizontal bar over basin)
        addMesh(new T.BoxGeometry(3, 3, basinD * 0.6), new T.MeshLambertMaterial({ color: '#cbd5e1' }), 0, c.h + 24, 0);
      } else if (el.type === 'stove') {
        // Body
        addMesh(new T.BoxGeometry(ew, c.h - 5, c.d), new T.MeshLambertMaterial({ color: '#374151' }), 0, (c.h - 5) / 2, 0);
        // Hob (flat top panel)
        addMesh(new T.BoxGeometry(ew + 2, 4, c.d + 2), new T.MeshLambertMaterial({ color: '#1f2937' }), 0, c.h - 2, 0);
        // 4 burner rings (dark iron circles approximated as thin cylinders)
        const burnerMat = new T.MeshLambertMaterial({ color: '#111827' });
        const burnerRingMat = new T.MeshLambertMaterial({ color: '#6b7280' });
        const bY = c.h + 1;
        const bOffX = ew * 0.26, bOffZ = c.d * 0.25;
        for (const [bx, bz] of [[-bOffX, -bOffZ], [bOffX, -bOffZ], [-bOffX, bOffZ], [bOffX, bOffZ]]) {
          // Outer ring
          addMesh(new T.CylinderGeometry(10, 10, 2.5, 16), burnerRingMat, bx, bY, bz);
          // Inner dark disc
          addMesh(new T.CylinderGeometry(6, 6, 3, 16), burnerMat, bx, bY, bz);
        }
        // Control knobs on front face
        const knobMat = new T.MeshLambertMaterial({ color: '#9ca3af' });
        for (let k = 0; k < 4; k++) {
          const kx = -ew * 0.35 + k * ew * 0.23;
          addMesh(new T.CylinderGeometry(3, 3, 4, 12), knobMat, kx, c.h * 0.5, c.d / 2 + 2);
        }
      } else if (el.type === 'fridge') {
        addMesh(new T.BoxGeometry(ew, c.h, c.d), new T.MeshLambertMaterial({ color: '#94a3b8' }), 0, c.h / 2, 0);
        addMesh(new T.BoxGeometry(4, c.h * 0.4, 4), new T.MeshLambertMaterial({ color: '#f8fafc' }), ew * 0.3, c.h * 0.6, c.d / 2 + 2);
      } else if (el.type === 'window') {
        addMesh(new T.BoxGeometry(ew, c.h, c.d), new T.MeshLambertMaterial({ color: '#bae6fd', transparent: true, opacity: 0.4, depthWrite: false }), 0, c.h / 2 + (c.elev || 0), 0);
      } else {
        addMesh(new T.BoxGeometry(ew, c.h, c.d), new T.MeshLambertMaterial({ color: c.color }), 0, c.h / 2 + (c.elev || 0), 0);
      }
      const sp = make3DSprite(T, c.name, '#fff', 18, 'rgba(0,0,0,0.6)');
      sp.position.set(0, c.h + (c.elev || 0) + 25, 0); eg.add(sp); g.add(eg);
    });

    // If Done was triggered while still in 2D, fire the upload now that the
    // scene geometry is built and the animation loop has had time to render.
    if (pendingDoneRef.current && ts.current.renderer) {
      pendingDoneRef.current = false;
      setTimeout(() => performDoneRef.current?.(), 600);
    }
  }, [walls, elements, mode, threeReady]);

  // ── 3D WIDE ANGLE ────────────────────────────────────────────────
  useEffect(() => {
    if (mode === '3d' && ts.current?.cam) {
      ts.current.cam.fov = wideAngle ? 80 : 45;
      ts.current.cam.updateProjectionMatrix();
    }
  }, [wideAngle, mode]);

  // ── DERIVED VALUES ───────────────────────────────────────────────
  const drawLen = drawing ? Math.round(Math.hypot(drawEnd.x - drawStart.x, drawEnd.y - drawStart.y)) : 0;
  const rooms = detectRooms(walls);
  let bbx1 = Infinity, bby1 = Infinity, bbx2 = -Infinity, bby2 = -Infinity;
  walls.forEach(w => { bbx1 = Math.min(bbx1, w.x1, w.x2); bbx2 = Math.max(bbx2, w.x1, w.x2); bby1 = Math.min(bby1, w.y1, w.y2); bby2 = Math.max(bby2, w.y1, w.y2); });
  const selWall = sel?.type === 'wall' ? walls.find(w => w.id === sel.id) : null;
  const selEl = sel?.type === 'element' ? elements.find(e => e.id === sel.id) : null;
  const selLen = selWall ? Math.round(Math.hypot(selWall.x2 - selWall.x1, selWall.y2 - selWall.y1)) : null;

  // Visual position getters — apply drag offset without committing
  const d = dragRef.current;
  const wallVis = w => {
    if (!d || d.id !== w.id || !d.moved) return w;
    if (d.kind === 'wall') return { ...w, x1: d.ox1 + d.dx, y1: d.oy1 + d.dy, x2: d.ox2 + d.dx, y2: d.oy2 + d.dy };
    if (d.kind === 'node') return { ...w, x1: d.node === 1 ? d.px : w.x1, y1: d.node === 1 ? d.py : w.y1, x2: d.node === 2 ? d.px : w.x2, y2: d.node === 2 ? d.py : w.y2 };
    return w;
  };
  const elVis = el => (d?.kind === 'el' && d.id === el.id && d.moved)
    ? { ...el, x: d.ox + d.dx, y: d.oy + d.dy } : el;

  // Cursor
  let cursor = 'default';
  if (spaceDown) cursor = panRef.current.active ? 'grabbing' : 'grab';
  else if (DRAW_TOOLS.includes(tool)) cursor = 'crosshair';
  else if (ITEMS[tool]) {
    if (!ghost) cursor = 'crosshair';
    else cursor = validateGhost(ghost, tool, elements, walls) ? 'copy' : 'not-allowed';
  }

  // Endpoint snap indicator (only for wall tools while drawing)
  const snapVis = (drawing && ENDPOINT_SNAP_TOOLS.includes(tool)) ? findEndpointSnap(rawMouse.x, rawMouse.y) : null;

  const groups = {};
  TOOL_DEFS.forEach(t => (groups[t.group] ??= []).push(t));

  // ── RENDER ───────────────────────────────────────────────────────
  return (
    <div className="flex h-screen w-full bg-[#18181b] text-slate-200 overflow-hidden" style={{ fontFamily: "'Inter',system-ui,sans-serif" }}>

      {/* SIDEBAR */}
      <div className={`${collapsed ? 'w-14' : 'w-60'} bg-[#18181b] border-r border-[#27272a] flex flex-col shadow-sm z-10 transition-all duration-200 flex-shrink-0 hidden sm:flex`}>
        <div className="p-4 border-b border-[#27272a] flex items-center justify-between">
          {!collapsed && <h1 className="font-bold text-[13px] tracking-wide text-slate-300">Please sketch your kitchen</h1>}
          <button onClick={() => setCollapsed(c => !c)} className="p-1.5 hover:bg-[#27272a] rounded-lg text-slate-500 hover:text-slate-300 ml-auto flex-shrink-0 transition-colors">
            {collapsed ? <ChevronRight size={14} /> : <ChevronLeft size={14} />}
          </button>
        </div>
        <div className="flex-1 overflow-y-auto p-2 space-y-3">
          {Object.entries(groups).map(([g, tools]) => (
            <div key={g}>
              {!collapsed && <p className="text-[10px] font-semibold text-slate-400 uppercase tracking-wider mb-1 px-1">{g}</p>}
              <div className={collapsed ? 'flex flex-col gap-1' : 'grid grid-cols-2 gap-1'}>
                {tools.map(t => (
                  <ToolBtn key={t.key} active={tool === t.key} small={collapsed}
                    onClick={() => setTool(t.key)} icon={t.icon} label={t.label} sc={t.sc}
                    onEnter={rect => setTooltip({ l: t.label, sc: t.sc, rect })}
                    onLeave={() => setTooltip(null)} />
                ))}
              </div>
            </div>
          ))}
          {/* Slider natively embedded when element is selected */}
          {ITEMS[tool] && !collapsed && (
            <div className="bg-red-950/20 border border-red-900/40 rounded-lg p-3 mt-2 animate-in fade-in slide-in-from-top-2 duration-300">
              <div className="flex items-center justify-between mb-3">
                <span className="text-[10px] font-bold text-red-500 uppercase tracking-wider">{ITEMS[tool].name} Width</span>
                <span className="text-[10px] font-mono text-red-400 bg-red-950/50 border border-red-900/50 px-1.5 py-0.5 rounded">
                  {Math.round(ITEMS[tool].w * (elWidths[tool] ?? 1))} cm
                </span>
              </div>
              <input type="range" min="0.5" max="2.5" step="0.05"
                value={elWidths[tool] ?? 1}
                onChange={e => setElWidths(w => ({ ...w, [tool]: parseFloat(e.target.value) }))}
                className="w-full accent-red-600 mb-1" />
            </div>
          )}
          <div className={`pt-3 border-t border-[#27272a] ${collapsed ? 'flex flex-col gap-1.5' : ''}`}>
            {!collapsed ? (
              <div className="flex bg-[#09090b] p-1 rounded-lg border border-[#27272a]">
                <button onClick={() => setMode('2d')} className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${mode === '2d' ? 'bg-[#27272a] shadow-sm text-red-500' : 'text-slate-500 hover:text-slate-400'}`}>2D Plan</button>
                <button onClick={() => setMode('3d')} className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${mode === '3d' ? 'bg-[#27272a] shadow-sm text-red-500' : 'text-slate-500 hover:text-slate-400'}`}>3D View</button>
              </div>
            ) : (
              <>
                <button onClick={() => setMode('2d')} className={`w-full p-2.5 rounded text-xs font-bold transition-colors ${mode === '2d' ? 'bg-red-950/40 text-red-500' : 'text-slate-500 hover:text-slate-400'}`}>2D</button>
                <button onClick={() => setMode('3d')} className={`w-full p-2.5 rounded text-xs font-bold transition-colors ${mode === '3d' ? 'bg-red-950/40 text-red-500' : 'text-slate-500 hover:text-slate-400'}`}>3D</button>
              </>
            )}
            {mode === '3d' && !collapsed && (
              <button 
                onClick={() => setWideAngle(w => !w)} 
                className={`mt-1.5 w-full flex items-center justify-center gap-2 py-1.5 text-xs font-semibold rounded-md transition-all border ${wideAngle ? 'bg-slate-800 text-slate-200 border-slate-600' : 'bg-[#18181b] text-slate-400 border-[#27272a] hover:text-slate-300'}`}
              >
                <Camera size={14} /> {wideAngle ? 'Standard Lens' : 'Wide Angle Lens'}
              </button>
            )}
          </div>
        </div>
        <div className="p-3 border-t border-[#27272a] bg-[#18181b] space-y-1.5">
          {!collapsed ? (
            <>
              <div className="flex gap-1">
                <SideBtn onClick={() => dispatch({ type: 'UNDO' })} disabled={!past.length}><Undo size={13} /> Undo</SideBtn>
                <SideBtn onClick={() => dispatch({ type: 'REDO' })} disabled={!future.length}><Redo size={13} /> Redo</SideBtn>
              </div>
              <div className="flex gap-1">
                <SideBtn onClick={exportJSON}><Save size={13} /> Save</SideBtn>
                <SideBtn onClick={() => fileRef.current?.click()}><Upload size={13} /> Load</SideBtn>
                <SideBtn onClick={exportPNG}><Download size={13} /> PNG</SideBtn>
              </div>
              {/* Auto Fill + Shuffle */}
              <div className="space-y-1 pt-1 border-t border-[#27272a]">
                <button
                  onClick={() => handleAutoFill()}
                  disabled={!walls.filter(w => w.type === 'solid').length}
                  className="w-full flex items-center justify-center gap-2 py-2 text-xs font-bold bg-gradient-to-r from-red-800 to-red-600 text-white rounded-lg hover:from-red-700 hover:to-red-500 disabled:opacity-30 disabled:cursor-not-allowed transition-all shadow-lg shadow-red-950/40">
                  ✨ Auto Fill Design
                </button>
                {lastAutoSeed !== null && (
                  <button
                    onClick={handleShuffle}
                    className="w-full flex items-center justify-center gap-2 py-1.5 text-xs font-semibold bg-[#27272a] border border-[#3f3f46] text-slate-300 rounded-lg hover:bg-[#3f3f46] hover:text-white transition-all">
                    🔀 Shuffle Layout
                  </button>
                )}
              </div>
              <button onClick={() => dispatch({ type: 'CLEAR' })} className="w-full flex items-center justify-center gap-1 py-1.5 text-xs text-red-600 hover:bg-red-950/30 rounded transition-colors"><Trash2 size={13} /> Clear All</button>

              {/* ── DONE button ── */}
              <button
                onClick={handleDone}
                disabled={doneState === 'uploading' || doneState === 'switching' || (!walls.length && !elements.length)}
                className="w-full flex items-center justify-center gap-2 py-2.5 mt-1 text-xs font-bold rounded-lg transition-all shadow-lg disabled:opacity-40 disabled:cursor-not-allowed"
                style={{
                  background: doneState === 'error'
                    ? 'linear-gradient(135deg,#7f1d1d,#991b1b)'
                    : 'linear-gradient(135deg,#065f46,#059669)',
                  color: '#fff',
                  boxShadow: '0 4px 20px rgba(5,150,105,0.35)',
                }}
              >
                {doneState === 'switching'  && '⏳ Switching to 3D…'}
                {doneState === 'uploading'  && '⏳ Uploading…'}
                {doneState === 'error'      && '❌ Failed — Retry'}
                {doneState === 'idle'       && '✓ Done / Send →'}
              </button>
            </>
          ) : (
            <>
              <IcoBtn onClick={() => dispatch({ type: 'UNDO' })} disabled={!past.length}><Undo size={14} /></IcoBtn>
              <IcoBtn onClick={() => dispatch({ type: 'REDO' })} disabled={!future.length}><Redo size={14} /></IcoBtn>
              <IcoBtn onClick={() => handleAutoFill()} title="Auto Fill"
                disabled={!walls.filter(w => w.type === 'solid').length}
                className="text-red-500 hover:bg-red-950/40">✨</IcoBtn>
              {lastAutoSeed !== null && (
                <IcoBtn onClick={handleShuffle} title="Shuffle" className="text-slate-300 hover:bg-[#3f3f46]">🔀</IcoBtn>
              )}
              <IcoBtn onClick={() => dispatch({ type: 'CLEAR' })} className="text-red-400 hover:bg-red-950/30"><Trash2 size={14} /></IcoBtn>
              {/* Done icon — collapsed sidebar */}
              <IcoBtn
                onClick={handleDone}
                title={doneState === 'switching' ? 'Switching…' : doneState === 'uploading' ? 'Uploading…' : 'Done / Send'}
                disabled={doneState === 'uploading' || doneState === 'switching' || (!walls.length && !elements.length)}
                className="text-emerald-400 hover:bg-emerald-950/40"
              >
                {doneState === 'idle' ? '✓' : '⏳'}
              </IcoBtn>
            </>
          )}
        </div>
      </div>

      {/* WORKSPACE */}
      <div className="flex-1 relative overflow-hidden" style={{ cursor }}>

        {/* 2D CANVAS */}
        <div className={`absolute inset-0 transition-opacity duration-200 ${mode === '2d' ? 'opacity-100 z-10' : 'opacity-0 pointer-events-none z-0'}`}>
          <svg ref={svgRef} className="w-full h-full touch-none select-none"
            onPointerDown={onDown} onPointerMove={onMove} onPointerUp={onUp}
            onPointerLeave={() => { panRef.current.active = false; if (dragRef.current) { dragRef.current = null; setDragTick(t => t + 1); } }}>

            {/* Grid */}
            <defs>
              <pattern id="g" width={GRID * view.s} height={GRID * view.s} patternUnits="userSpaceOnUse"
                x={view.x % (GRID * view.s)} y={view.y % (GRID * view.s)}>
                <path d={`M ${GRID * view.s} 0 L 0 0 0 ${GRID * view.s}`} fill="none" stroke="#27272a" strokeWidth="1" />
              </pattern>
            </defs>
            <rect width="100%" height="100%" fill="#18181b" />
            <rect width="100%" height="100%" fill="url(#g)" opacity="0.6" />

            <g transform={`translate(${view.x},${view.y}) scale(${view.s})`}>

              {/* Floor tint — warm cream so the room interior glows against dark background */}
              {walls.length > 0 && <rect x={bbx1 - 20} y={bby1 - 20} width={bbx2 - bbx1 + 40} height={bby2 - bby1 + 40} fill="#fef9ee" opacity={0.92} rx={4} />}

              {/* Room areas */}
              {rooms.map((r, i) => {
                const a = (polyArea(r) / 10000).toFixed(2), c = centroid(r);
                return <g key={`r${i}`}><polygon points={r.map(p => `${p.x},${p.y}`).join(' ')} fill="#dbeafe" opacity={0.2} /><text x={c.x} y={c.y} fontSize={12} fill="#1d4ed8" textAnchor="middle" fontWeight="700" opacity={0.8}>{a} m²</text></g>;
              })}

              {/* Countertop lip on base cabs (both sides) */}
              {walls.filter(w => w.type === 'base_cab').map(w => {
                const vw = wallVis(w), a = Math.atan2(vw.y2 - vw.y1, vw.x2 - vw.x1);
                const nx = -Math.sin(a) * 32, ny = Math.cos(a) * 32;
                return <g key={`ct${w.id}`}>
                  <line x1={vw.x1 + nx} y1={vw.y1 + ny} x2={vw.x2 + nx} y2={vw.y2 + ny} stroke="#78716c" strokeWidth={2} opacity={0.5} />
                  <line x1={vw.x1 - nx} y1={vw.y1 - ny} x2={vw.x2 - nx} y2={vw.y2 - ny} stroke="#78716c" strokeWidth={2} opacity={0.5} />
                </g>;
              })}

              {/* Render layers — bottom to top */}
              {walls.filter(w => w.type === 'virtual').map(w => <WallSVG key={w.id} w={wallVis(w)} sel={sel?.id === w.id} />)}
              {walls.filter(w => w.type === 'solid').map(w => <WallSVG key={w.id} w={wallVis(w)} sel={sel?.id === w.id} />)}
              {walls.filter(w => w.type === 'short').map(w => <WallSVG key={w.id} w={wallVis(w)} sel={sel?.id === w.id} />)}
              {/* Doors sit in the wall opening */}
              {elements.filter(e => e.type === 'door').map(el => <ElSVG key={el.id} el={elVis(el)} sel={sel?.id === el.id} />)}
              {walls.filter(w => w.type === 'base_cab').map(w => <WallSVG key={w.id} w={wallVis(w)} sel={sel?.id === w.id} />)}
              {/* Appliances sit on base cabs */}
              {elements.filter(e => ['fridge', 'sink', 'stove', 'cupboard'].includes(e.type)).map(el => <ElSVG key={el.id} el={elVis(el)} sel={sel?.id === el.id} />)}
              {walls.filter(w => w.type === 'upper_cab').map(w => <WallSVG key={w.id} w={wallVis(w)} sel={sel?.id === w.id} />)}
              {/* Windows always on top — visible regardless of draw order */}
              {elements.filter(e => e.type === 'window').map(el => <ElSVG key={el.id} el={elVis(el)} sel={sel?.id === el.id} />)}

              {/* Warnings */}
              {warnings.map((w, i) => (
                <g key={`warn${i}`} transform={`translate(${w.x},${w.y - 30})`}>
                  <polygon points="0,-10 8,5 -8,5" fill="#f97316" opacity={0.9} />
                  <text x={0} y={3} fontSize={7} fill="white" textAnchor="middle" fontWeight="bold">!</text>
                </g>
              ))}

              {/* Active drawing */}
              {drawing && (() => {
                const valid = validateLine(drawStart, drawEnd, tool, elements);
                let col = valid ? '#3b82f6' : '#ef4444', w = WALL_T, dash = 'none', cap = 'round', op = valid ? 0.7 : 0.9;
                let sx = 0, sy = 0;
                if (valid) {
                  if (tool === 'virtual_wall') { col = '#ef4444'; dash = '8,8'; w = 2; }
                  else if (tool === 'short_wall') { col = '#94a3b8'; w = 60; cap = 'butt'; }
                  else if (tool === 'base_cab' || tool === 'upper_cab') {
                    col = tool === 'base_cab' ? '#d97706' : '#b45309';
                    w = tool === 'base_cab' ? 60 : 30; cap = 'butt'; op = 0.5;
                    if (tool === 'upper_cab') dash = '4,4';
                    const tracing = walls.some(wl => ['solid', 'short'].includes(wl.type) &&
                      ptSeg(drawStart.x, drawStart.y, wl.x1, wl.y1, wl.x2, wl.y2).dist < 15 &&
                      ptSeg(drawEnd.x, drawEnd.y, wl.x1, wl.y1, wl.x2, wl.y2).dist < 15);
                    if (tracing && (drawStart.x !== drawEnd.x || drawStart.y !== drawEnd.y)) {
                      const o = dynOffset(drawStart.x, drawStart.y, drawEnd.x, drawEnd.y, rawMouse.x, rawMouse.y, w);
                      sx = o.sx; sy = o.sy;
                    }
                  }
                }
                return <g>
                  <line x1={drawStart.x + sx} y1={drawStart.y + sy} x2={drawEnd.x + sx} y2={drawEnd.y + sy}
                    stroke={col} strokeWidth={w} strokeLinecap={cap} strokeDasharray={dash} opacity={op} />
                  {drawLen > 0 && (
                    <g transform={`translate(${(drawStart.x + drawEnd.x) / 2 + sx},${(drawStart.y + drawEnd.y) / 2 + sy - 18})`}>
                      <rect x={-28} y={-11} width={56} height={20} rx={5} fill={valid ? '#1e293b' : '#ef4444'} opacity={0.9} />
                      <text x={0} y={4} fill="white" fontSize={10} fontWeight="bold" textAnchor="middle">{drawLen} cm</text>
                    </g>
                  )}
                  {snapVis && <circle cx={snapVis.x} cy={snapVis.y} r={6} fill="none" stroke="#22c55e" strokeWidth={2} />}
                </g>;
              })()}

              {/* Ghost element — width reflects slider in real time */}
              {ghost && ITEMS[tool] && (() => {
                const ok = validateGhost(ghost, tool, elements, walls), it = ITEMS[tool];
                const gw = it.w * (elWidths[tool] ?? 1);  // scaled ghost width
                return <g transform={`translate(${ghost.x},${ghost.y}) rotate(${ghost.rotation * 180 / Math.PI})`} opacity={ok ? 0.55 : 0.8}>
                  <rect x={-gw / 2} y={-it.d / 2} width={gw} height={it.d}
                    fill={ok ? it.color : '#fee2e2'} stroke={ok ? '#3b82f6' : '#ef4444'}
                    strokeWidth={2} strokeDasharray="4,4" rx={2} />
                  {ghost.snapped && ok && <circle cx={0} cy={-it.d / 2 - 8} r={3} fill="#22c55e" />}
                </g>;
              })()}

              {/* Delete button on selected */}
              {selEl && (() => {
                const ve = elVis(selEl), it = ITEMS[ve.type];
                return <g transform={`translate(${ve.x + (it?.w ?? 40) / 2 + 12},${ve.y - (it?.d ?? 40) / 2 - 12})`}
                  onClick={() => dispatch({ type: 'DEL_EL', p: selEl.id })} style={{ cursor: 'pointer' }}>
                  <circle r={9} fill="#ef4444" /><text x={0} y={4} fontSize={11} fill="white" textAnchor="middle" fontWeight="bold">×</text>
                </g>;
              })()}
              {selWall && <g transform={`translate(${(selWall.x1 + selWall.x2) / 2 + 14},${(selWall.y1 + selWall.y2) / 2 - 14})`}
                onClick={() => dispatch({ type: 'DEL_WALL', p: selWall.id })} style={{ cursor: 'pointer' }}>
                <circle r={9} fill="#ef4444" /><text x={0} y={4} fontSize={11} fill="white" textAnchor="middle" fontWeight="bold">×</text>
              </g>}
            </g>
          </svg>

          {/* Empty state */}
          {!walls.length && !elements.length && (
            <div className="absolute inset-0 flex items-center justify-center pointer-events-none">
              <div className="text-center opacity-40">
                <p className="text-base font-semibold text-slate-400">Draw your first wall</p>
                <p className="text-xs text-slate-500 mt-1">Select <strong>Wall (W)</strong> then drag on the canvas</p>
              </div>
            </div>
          )}

          {/* Hint bar */}
          <div className="absolute top-4 left-1/2 -translate-x-1/2 bg-[#27272a]/90 backdrop-blur-md px-4 py-2 rounded-full shadow-lg border border-[#3f3f46] text-[11px] text-slate-300 pointer-events-none whitespace-nowrap">
            {tool === 'select' && !drawing && sel?.type === 'wall' && 'Drag blue ◆ handles to resize · Drag body to move'}
            {tool === 'select' && !drawing && !sel && 'Click to select · Drag to move · Delete to remove'}
            {tool === 'select' && !drawing && sel?.type !== 'wall' && sel && 'Drag to move · Delete to remove'}
            {DRAW_TOOLS.includes(tool) && !drawing && 'Drag to draw · Shift = axis-lock'}
            {drawing && 'Release to place · Escape to cancel'}
            {ITEMS[tool] && !drawing && 'Click to place · Moves near walls automatically'}
          </div>

          {/* Zoom controls */}
          <div className="absolute bottom-12 right-5 flex flex-col gap-1.5 z-20">
            <ZoomBtn onClick={fitView} title="Fit to view"><Maximize2 size={14} /></ZoomBtn>
            <ZoomBtn onClick={() => zoomBtn(1)} title="Zoom in"><ZoomIn size={14} /></ZoomBtn>
            <ZoomBtn onClick={() => zoomBtn(-1)} title="Zoom out"><ZoomOut size={14} /></ZoomBtn>
          </div>

          {/* Status bar */}
          <div className="absolute bottom-0 left-0 right-0 h-8 bg-[#18181b]/95 backdrop-blur border-t border-[#27272a] flex items-center px-4 gap-5 text-[10px] text-slate-400 z-20 overflow-x-auto whitespace-nowrap shadow-xl">
            <span className="font-semibold text-red-500 uppercase tracking-widest">{TOOL_DEFS.find(t => t.key === tool)?.label}</span>
            <span>{Math.round(view.s * 100)}%</span>
            {selLen != null && <span>Wall: <b className="text-slate-300">{selLen} cm</b></span>}
            {selEl && <span>{ITEMS[selEl.type]?.name} <span className="text-slate-500">({Math.round(selEl.x)}, {Math.round(selEl.y)})</span></span>}
            {rooms.length > 0 && <span className="text-slate-300">{rooms.map((r, i) => `${(polyArea(r) / 10000).toFixed(1)}m²`).join(' · ')}</span>}
            {warnings.length > 0 && <span className="text-red-500 flex items-center gap-1 font-medium"><AlertTriangle size={11} /> {warnings.length}</span>}
            <span className="ml-auto text-slate-500 font-mono text-[9px]">{past.length}↩ {future.length}↪</span>
          </div>
        </div>

        {/* 3D */}
        <div className={`absolute inset-0 bg-slate-900 transition-opacity duration-200 ${mode === '3d' ? 'opacity-100 z-10' : 'opacity-0 pointer-events-none z-0'}`}>
          <div ref={threeMount} className="w-full h-full cursor-move" />
          <div className="absolute top-3 left-3 bg-black/50 backdrop-blur px-3 py-1.5 rounded-lg text-xs text-white/80 pointer-events-none flex items-center gap-1.5">
            <Info size={12} /> Drag to rotate · Scroll to zoom
          </div>
        </div>

        {/* Mobile toolbar */}
        <div className="sm:hidden fixed bottom-0 left-0 right-0 bg-white border-t border-slate-200 flex justify-around z-30" style={{ paddingBottom: 'env(safe-area-inset-bottom, 0px)' }}>
          {[TOOL_DEFS[0], TOOL_DEFS[1], TOOL_DEFS[6], TOOL_DEFS[8], TOOL_DEFS[9]].map(t => (
            <button key={t.key} onClick={() => setTool(t.key)}
              className={`flex flex-col items-center py-2 px-3 text-[9px] gap-0.5 ${tool === t.key ? 'text-blue-600' : 'text-slate-500'}`}>
              {t.icon}<span>{t.label}</span>
            </button>
          ))}
          <button onClick={() => setMode(m => m === '2d' ? '3d' : '2d')}
            className="flex flex-col items-center py-2 px-3 text-[9px] gap-0.5 text-slate-500">
            <Box3D size={18} /><span>{mode === '2d' ? '3D' : '2D'}</span>
          </button>
          {/* Done — mobile */}
          <button
            onClick={handleDone}
            disabled={doneState === 'uploading' || doneState === 'switching' || (!walls.length && !elements.length)}
            className="flex flex-col items-center py-2 px-3 text-[9px] gap-0.5 font-bold text-emerald-600 disabled:opacity-40">
            <span style={{ fontSize: 18, lineHeight: 1 }}>✓</span>
            <span>{doneState === 'idle' ? 'Done' : doneState === 'error' ? 'Retry' : '…'}</span>
          </button>
        </div>
      </div>

      {tooltip && <div className="fixed z-50 bg-slate-800 text-white text-[11px] px-2 py-1 rounded shadow pointer-events-none" style={{ left: tooltip.rect.right + 8, top: tooltip.rect.top + tooltip.rect.height / 2 - 12 }}>{tooltip.l}{tooltip.sc ? ` (${tooltip.sc})` : ''}</div>}
      {saveMsg && <div className="fixed bottom-12 left-1/2 -translate-x-1/2 bg-emerald-600 text-white text-xs px-4 py-2 rounded-full shadow-lg z-50 pointer-events-none">✓ Saved</div>}
      {autoMsg && <div className="fixed bottom-20 left-1/2 -translate-x-1/2 bg-[#27272a] border border-[#3f3f46] text-slate-200 text-xs font-semibold px-5 py-2.5 rounded-full shadow-2xl z-50 pointer-events-none">{autoMsg}</div>}

      <input ref={fileRef} type="file" accept=".json" className="hidden" onChange={importJSON} />
    </div>
  );
}

// =============================================================================
// SVG COMPONENTS (pure render, no click handlers — selection via pointerDown)
// =============================================================================
function WallSVG({ w, sel }) {
  let col = '#1e293b', dash = 'none', wid = WALL_T, cap = 'round', op = 1;
  if (w.type === 'virtual') { col = '#ef4444'; dash = '8,8'; wid = 2; }
  else if (w.type === 'short') { col = '#94a3b8'; wid = 60; cap = 'butt'; }
  else if (w.type === 'base_cab') { col = '#d97706'; wid = 60; cap = 'butt'; }
  else if (w.type === 'upper_cab') { col = '#b45309'; wid = 30; cap = 'butt'; dash = '4,4'; op = 0.9; }
  const mx = (w.x1 + w.x2) / 2, my = (w.y1 + w.y2) / 2;
  const len = Math.round(Math.hypot(w.x2 - w.x1, w.y2 - w.y1));
  const ang = Math.atan2(w.y2 - w.y1, w.x2 - w.x1);
  const px = -Math.sin(ang) * 18, py = Math.cos(ang) * 18;

  // Cabinet module dividers — one tick every 60cm along the run
  const isCab = w.type === 'base_cab' || w.type === 'upper_cab';
  const MODULE = 60;
  const cabTicks = [];
  if (isCab && len > MODULE) {
    const dx = (w.x2 - w.x1) / len, dy = (w.y2 - w.y1) / len;
    // perpendicular direction (across cabinet thickness)
    const nx = -dy, ny = dx;
    const half = wid / 2;
    // Number of dividers = Math.floor(len / MODULE) - 1 (skip endpoints)
    const count = Math.floor(len / MODULE);
    for (let i = 1; i < count; i++) {
      const t = i * MODULE;
      const cx = w.x1 + dx * t, cy = w.y1 + dy * t;
      cabTicks.push(
        <line key={i}
          x1={cx - nx * half} y1={cy - ny * half}
          x2={cx + nx * half} y2={cy + ny * half}
          stroke={w.type === 'base_cab' ? '#b45309' : '#92400e'}
          strokeWidth={1.2} opacity={0.6} />
      );
    }
  }

  return <g>
    <line x1={w.x1} y1={w.y1} x2={w.x2} y2={w.y2} stroke={col} strokeWidth={wid} strokeLinecap={cap} strokeDasharray={dash} opacity={op} />
    {cabTicks}
    {sel && <>
      <line x1={w.x1} y1={w.y1} x2={w.x2} y2={w.y2} stroke="#3b82f6" strokeWidth={wid + 8} strokeLinecap={cap} strokeDasharray="6,4" opacity={0.4} fill="none" />
      {/* Visible resize handle */}
      <rect x={w.x1 - 8} y={w.y1 - 8} width={16} height={16} fill="#3b82f6" rx={3} />
      <rect x={w.x2 - 8} y={w.y2 - 8} width={16} height={16} fill="#3b82f6" rx={3} />
      {/* Transparent pointer-target — 28px hit area ensures easy clicking */}
      <rect x={w.x1 - 14} y={w.y1 - 14} width={28} height={28} fill="transparent" style={{cursor: 'nwse-resize'}} />
      <rect x={w.x2 - 14} y={w.y2 - 14} width={28} height={28} fill="transparent" style={{cursor: 'nwse-resize'}} />
    </>}
    {(w.type === 'solid' || w.type === 'short') && len > 30 && (
      <g transform={`translate(${mx + px},${my + py})`}>
        <rect x={-22} y={-9} width={44} height={18} rx={4} fill="#f1f5f9" stroke="#e2e8f0" strokeWidth={0.5} />
        <text x={0} y={4} fontSize={9} fill="#64748b" textAnchor="middle" fontWeight="600">{len}</text>
      </g>
    )}
  </g>;
}


function ElSVG({ el, sel, elWidths = {} }) {
  const c = ITEMS[el.type]; if (!c) return null;
  const deg = el.rotation * 180 / Math.PI;
  // Effective width — use stored scaleW (set at placement) if available
  const sw = el.scaleW ?? 1;
  const EW = c.w * sw;  // rendered width

  if (el.type === 'window') {
    const W = EW, D = c.d;
    const hw = W / 2, hd = D / 2;
    const frameT = 3, sillH = 4;
    return (
      <g transform={`translate(${el.x},${el.y}) rotate(${deg})`}>
        <rect x={-hw} y={-hd} width={W} height={D} fill="#bae6fd" opacity={0.55} rx={1} />
        <rect x={-hw} y={-hd} width={W} height={D} fill="none" stroke="#1e293b" strokeWidth={frameT} rx={1} />
        <line x1={0} y1={-hd + frameT} x2={0} y2={hd - frameT} stroke="#1e293b" strokeWidth={1.5} />
        <line x1={-hw + frameT} y1={0} x2={hw - frameT} y2={0} stroke="#1e293b" strokeWidth={1.5} />
        <rect x={-hw - 2} y={hd} width={W + 4} height={sillH} fill="#94a3b8" rx={1} />
        <line x1={-hw + frameT + 3} y1={-hd + frameT + 3} x2={-hw + frameT + 3} y2={-2} stroke="white" strokeWidth={1.5} opacity={0.5} strokeLinecap="round" />
        {sel && <rect x={-hw - 5} y={-hd - 5} width={W + 10} height={D + 10} fill="none" stroke="#3b82f6" strokeWidth={1.5} strokeDasharray="5,3" rx={4} />}
        <text x={0} y={4} fontSize={9} fill="#0369a1" textAnchor="middle" fontWeight="700" transform={`rotate(${-deg})`}>WIN</text>
      </g>
    );
  }

  return <g transform={`translate(${el.x},${el.y}) rotate(${deg})`}>
    {/* Main body */}
    <rect x={-EW / 2} y={-c.d / 2} width={EW} height={c.d}
      fill={c.color} stroke={sel ? '#3b82f6' : '#334155'} strokeWidth={sel ? 2 : 0.5} rx={2} />
    {sel && <rect x={-EW / 2 - 5} y={-c.d / 2 - 5} width={EW + 10} height={c.d + 10}
      fill="none" stroke="#3b82f6" strokeWidth={1.5} strokeDasharray="5,3" rx={4} />}

    {el.type === 'sink' && <>
      {/* Basin rectangle */}
      <rect x={-EW / 2 + 10} y={-c.d / 2 + 14} width={EW - 20} height={c.d - 24}
        fill="#f1f5f9" stroke="#94a3b8" strokeWidth={1} rx={3} />
      {/* Drain circle */}
      <circle cx={0} cy={4} r={5} fill="none" stroke="#94a3b8" strokeWidth={1.5} />
      <circle cx={0} cy={4} r={2} fill="#94a3b8" />
      {/* Faucet tap */}
      <rect x={-3} y={-c.d / 2 + 4} width={6} height={8} fill="#cbd5e1" rx={1} />
      <rect x={-8} y={-c.d / 2 + 4} width={16} height={3} fill="#cbd5e1" rx={1} />
    </>}

    {el.type === 'stove' && <>
      {/* Hob surface */}
      <rect x={-EW / 2 + 3} y={-c.d / 2 + 3} width={EW - 6} height={c.d - 6}
        fill="#1f2937" rx={2} />
      {/* 4 burners */}
      {[[-0.27, -0.27], [0.27, -0.27], [-0.27, 0.27], [0.27, 0.27]].map(([fx, fy], i) => (
        <g key={i} transform={`translate(${EW * fx}, ${c.d * fy})`}>
          <circle r={9} fill="none" stroke="#4b5563" strokeWidth={2} />
          <circle r={4} fill="#374151" />
        </g>
      ))}
      {/* Control strip */}
      <rect x={-EW / 2 + 6} y={c.d / 2 - 9} width={EW - 12} height={5} fill="#4b5563" rx={1} />
      {[-0.3, -0.1, 0.1, 0.3].map((f, i) => (
        <circle key={i} cx={EW * f} cy={c.d / 2 - 6.5} r={2.5} fill="#9ca3af" />
      ))}
    </>}

    {el.type === 'fridge' && <line x1={-EW / 2 + 8} y1={c.d / 2 - 6} x2={EW / 2 - 8} y2={c.d / 2 - 6} stroke="#334155" strokeWidth={3} strokeLinecap="round" />}

    {el.type === 'cupboard' && <>
      {/* Two door panels */}
      <line x1={0} y1={-c.d / 2 + 2} x2={0} y2={c.d / 2 - 2} stroke="#78350f" strokeWidth={1.5} />
      <rect x={-EW / 2 + 3} y={-c.d / 2 + 3} width={EW / 2 - 5} height={c.d - 6} fill="none" stroke="#78350f" strokeWidth={1} rx={1} />
      <rect x={2} y={-c.d / 2 + 3} width={EW / 2 - 5} height={c.d - 6} fill="none" stroke="#78350f" strokeWidth={1} rx={1} />
      {/* Handles */}
      <circle cx={-6} cy={0} r={2.5} fill="#92400e" />
      <circle cx={6}  cy={0} r={2.5} fill="#92400e" />
    </>}
    {el.type === 'door' && (() => {
      const sw2 = el.swing ?? 1, r = EW;
      const hy = sw2 > 0 ? c.d / 2 : -c.d / 2;
      return <path d={`M ${EW / 2} ${hy} A ${r} ${r} 0 0 ${sw2 > 0 ? 1 : 0} ${-EW / 2} ${hy + sw2 * r}`}
        fill="none" stroke="#8b4513" strokeWidth={1} strokeDasharray="3,3" opacity={0.7} />;
    })()}
    <text x={0} y={4} fontSize={10} fill="#1e293b" textAnchor="middle" fontWeight="bold" transform={`rotate(${-deg})`}>{c.name}</text>
  </g>;
}

// =============================================================================
// TINY UI COMPONENTS
// =============================================================================
function ToolBtn({ active, small, onClick, icon, label, sc, onEnter, onLeave }) {
  const r = useRef(null);
  return <button ref={r} onClick={onClick}
    onMouseEnter={() => onEnter?.(r.current?.getBoundingClientRect())}
    onMouseLeave={onLeave}
    className={`flex items-center justify-center gap-1.5 rounded-lg border transition-all text-xs font-semibold
      ${small ? 'p-2 w-full' : 'px-2 py-2 flex-col'}
      ${active ? 'bg-red-950/40 border-red-900 text-red-500 shadow-inner' : 'bg-[#18181b] border-transparent text-slate-400 hover:bg-[#27272a] hover:text-slate-300'}`}>
    {icon}{!small && <span className="text-[9px] leading-tight mt-0.5">{label}</span>}
  </button>;
}
function SideBtn({ children, ...p }) { return <button {...p} className={`flex-1 flex items-center justify-center gap-1 py-1.5 text-[11px] text-slate-400 hover:bg-[#27272a] hover:text-slate-200 rounded disabled:opacity-30 transition-colors ${p.className ?? ''}`}>{children}</button>; }
function IcoBtn({ children, className = '', ...p }) { return <button {...p} className={`w-full p-2 flex justify-center text-slate-400 hover:bg-[#27272a] hover:text-slate-200 rounded disabled:opacity-30 transition-colors ${className}`}>{children}</button>; }
function ZoomBtn({ children, ...p }) { return <button {...p} className="w-8 h-8 flex items-center justify-center bg-[#18181b] border border-[#27272a] rounded-lg shadow-lg text-slate-400 hover:text-slate-200 hover:bg-[#27272a] transition-all">{children}</button>; }
