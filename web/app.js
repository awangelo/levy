// The page: it hands scripts to the WebAssembly stepper and draws the frames
// that come back. All of the reduction logic lives on the Rust side.

import init, { Session } from "./pkg/levy_web.js";

const SVG = "http://www.w3.org/2000/svg";
const COLUMN = 62; // horizontal distance between neighbouring leaves
const ROW = 58; // vertical distance between a node and its children
const MARGIN = 44;
const MAX_DRAWN = 700; // nets with more nodes are not drawn
const MAX_BATCH = 50_000; // steps "Next β" and "Finish" fire before giving up

const RADIUS = { root: 4, lam: 15, app: 15, fan: 15, delim: 13, eraser: 8, free: 14 };

const RULES = {
  beta: ["β", "an application meets its abstraction. Both vanish, and two delimiters mark the scope the abstraction used to bind."],
  annihilate: ["Annihilate", "two fans or two delimiters of the same level meet and cancel out."],
  commute: ["Commute", "the two nodes pass through each other. Each is copied once per auxiliary port of the other."],
  dissolve: ["Dissolve", "a delimiter reaches the root or a free variable and vanishes."],
};

const PRELUDE = `true  = \\a b. a
false = \\a b. b
times = \\m n f. m (n f)
iszero = \\n. n (\\x. false) true
pred  = \\n f x. n (\\g h. h (g f)) (\\u. x) (\\u. u)
fix   = \\f. (\\x. f (x x)) (\\x. f (x x))
fact  = fix (\\self n. iszero n 1 (times n (self (pred n))))
`;

const EXAMPLES = [
  ["A shared redex", "-- The argument is used twice but reduced once.\n(\\x. f x x) ((\\y. y) a)\n"],
  ["Two applied to two", "two = \\f x. f (f x)\ntwo two\n"],
  ["Identity", "(\\x. x) y\n"],
  ["Erasure beats divergence", "-- The argument loops forever, but nothing needs it.\n(\\x. y) ((\\x. x x) (\\x. x x))\n"],
  ["Sharing under a binder", "-- Copying the abstraction must not copy the redex inside it.\n(\\f. f (f a)) (\\x. (\\y. y) x)\n"],
  ["Lamping's example", "(\\g. g (g (\\x. x))) (\\h. (\\f. f (f (\\z. z))) (\\w. h (w (\\y. y))))\n"],
  ["An abstraction inside its own copy", "\\x. (\\f. f f) (\\g. x (\\y. g y))\n"],
  ["Exponentiation", "-- 2 ^ (2 ^ 2), then applied to two identities.\n2 2 2 (\\x. x) (\\x. x)\n"],
  ["Factorial of two", `${PRELUDE}\nfact 2\n`],
];

const $ = (id) => document.getElementById(id);
const ui = {
  examples: $("examples"),
  script: $("script"),
  load: $("load"),
  problem: $("problem"),
  reset: $("reset"),
  back: $("back"),
  step: $("step"),
  beta: $("beta"),
  play: $("play"),
  finish: $("finish"),
  fit: $("fit"),
  speed: $("speed"),
  net: $("net"),
  wires: $("wires"),
  nodes: $("nodes"),
  oversize: $("oversize"),
  term: $("term"),
  next: $("next"),
  statBeta: $("stat-beta"),
  statBookkeeping: $("stat-bookkeeping"),
  statNodes: $("stat-nodes"),
  statCollected: $("stat-collected"),
};

let session = null;
let frame = null; // the frame on screen
let drawn = { nodes: [], wires: [] }; // its SVG elements
let positions = new Map(); // node id -> where it is drawn right now
let view = null; // the viewBox right now
let following = true; // whether the view keeps the whole net in sight
let animation = 0; // identifies the running animation; bumping it cancels
let timer = null; // set while playing

function svg(name, attributes, parent) {
  const element = document.createElementNS(SVG, name);
  for (const [key, value] of Object.entries(attributes)) element.setAttribute(key, value);
  parent?.append(element);
  return element;
}

// ---------------------------------------------------------------- drawing

function describe(node) {
  switch (node.kind) {
    case "lam":
      return `abstraction λ${node.label}`;
    case "app":
      return "application";
    case "fan":
      return `fan, level ${node.level}`;
    case "delim":
      return `delimiter, level ${node.level}`;
    case "eraser":
      return "eraser: nothing uses this port";
    case "free":
      return `free variable ${node.label}`;
    default:
      return "root";
  }
}

function short(label) {
  return label.length > 3 ? `${label.slice(0, 2)}…` : label;
}

// Builds the SVG group of one node. Fans and delimiters get a part that is
// turned towards whatever their principal port faces.
function buildNode(node, isNext) {
  const group = svg("g", { class: `node ${node.kind}${isNext ? " next" : ""}` }, ui.nodes);
  svg("title", {}, group).textContent = describe(node);
  let turning = null;
  let text = "";
  switch (node.kind) {
    case "lam":
      svg("circle", { class: "shape", r: RADIUS.lam }, group);
      text = `λ${short(node.label)}`;
      break;
    case "app":
      svg("circle", { class: "shape", r: RADIUS.app }, group);
      text = "@";
      break;
    case "fan":
      turning = svg("g", {}, group);
      svg("path", { class: "shape", d: "M0,-16 L15,10 L-15,10 Z", "stroke-linejoin": "round" }, turning);
      text = String(node.level);
      break;
    case "delim":
      turning = svg("g", {}, group);
      svg("path", { class: "shape", d: "M-14,6 A14,14 0 0 1 14,6 Z", "stroke-linejoin": "round" }, turning);
      text = String(node.level);
      break;
    case "eraser":
      svg("circle", { class: "shape", r: RADIUS.eraser }, group);
      text = "×";
      break;
    case "free": {
      const width = Math.max(28, 9 * node.label.length + 12);
      svg("rect", { class: "shape", x: -width / 2, y: -12, width, height: 24, rx: 12 }, group);
      text = node.label;
      break;
    }
    default:
      svg("circle", { class: "shape", r: RADIUS.root }, group);
  }
  if (text) svg("text", {}, group).textContent = text;
  return { id: node.id, kind: node.kind, group, turning, faces: null };
}

function buildWire(wire, isNext) {
  const kind = wire.tree ? "" : " back";
  const path = svg("path", { class: `wire${kind}${isNext ? " next" : ""}` }, ui.wires);
  const dot = () => svg("circle", { class: `port${isNext ? " next" : ""}`, r: 3.2 }, ui.wires);
  return {
    ...wire,
    path,
    dotA: wire.a_port === 0 && wire.a !== wire.b ? dot() : null,
    dotB: wire.b_port === 0 && wire.a !== wire.b ? dot() : null,
  };
}

// The path of a wire and the point its curve bends towards, if it bends.
function route(wire, a, b) {
  if (wire.a === wire.b) {
    // A wire from a node to itself, as in the identity: a loop underneath.
    return { d: `M${a.x + 9},${a.y + 11} C${a.x + 44},${a.y + 62} ${a.x - 44},${a.y + 62} ${a.x - 9},${a.y + 11}`, bend: null };
  }
  if (wire.tree) return { d: `M${a.x},${a.y} L${b.x},${b.y}`, bend: null };
  const [upper, lower] = a.y <= b.y ? [a, b] : [b, a];
  const length = Math.hypot(b.x - a.x, b.y - a.y);
  const side = lower.x >= upper.x ? 1 : -1;
  const bend = {
    x: (a.x + b.x) / 2 + side * Math.min(80, Math.max(22, length * 0.3)),
    y: (a.y + b.y) / 2,
  };
  return { d: `M${a.x},${a.y} Q${bend.x},${bend.y} ${b.x},${b.y}`, bend };
}

// Puts the marker of a principal port on the rim of its node, on the wire.
function placeDot(dot, from, towards, radius) {
  if (!dot) return;
  const length = Math.hypot(towards.x - from.x, towards.y - from.y) || 1;
  dot.setAttribute("cx", from.x + ((towards.x - from.x) / length) * radius);
  dot.setAttribute("cy", from.y + ((towards.y - from.y) / length) * radius);
}

// Moves every element to the given positions.
function place(at) {
  for (const node of drawn.nodes) {
    const here = at.get(node.id);
    node.group.setAttribute("transform", `translate(${here.x},${here.y})`);
    const target = node.turning && node.faces !== null ? at.get(node.faces) : null;
    if (target) {
      const angle = (Math.atan2(target.y - here.y, target.x - here.x) * 180) / Math.PI + 90;
      node.turning.setAttribute("transform", `rotate(${angle})`);
    }
  }
  for (const wire of drawn.wires) {
    const a = at.get(wire.a);
    const b = at.get(wire.b);
    const { d, bend } = route(wire, a, b);
    wire.path.setAttribute("d", d);
    placeDot(wire.dotA, a, bend ?? b, RADIUS[wire.kindA]);
    placeDot(wire.dotB, b, bend ?? a, RADIUS[wire.kindB]);
  }
}

function boundsOf(points) {
  let [left, top, right, bottom] = [Infinity, Infinity, -Infinity, -Infinity];
  for (const { x, y } of points) {
    left = Math.min(left, x);
    right = Math.max(right, x);
    top = Math.min(top, y);
    bottom = Math.max(bottom, y);
  }
  // Keep a minimum extent so that tiny nets are not blown up to fill the page.
  const width = Math.max(right - left, 5 * COLUMN);
  const height = Math.max(bottom - top, 4 * ROW);
  return {
    x: (left + right) / 2 - width / 2 - MARGIN,
    y: top - MARGIN,
    w: width + 2 * MARGIN,
    h: height + 2 * MARGIN + 30,
  };
}

const mix = (from, to, t) => from + (to - from) * t;
const ease = (t) => 1 - (1 - t) ** 3;

function duration() {
  const slow = 1 - Number(ui.speed.value) / 100;
  return 40 + 900 * slow * slow;
}

// Shows `next`, moving from what is on screen. Nodes that are new start at
// `spawn`, the place of the pair whose interaction created them.
function draw(next, animate, spawn) {
  frame = next;
  ui.wires.replaceChildren();
  ui.nodes.replaceChildren();
  drawn = { nodes: [], wires: [] };

  const oversize = next.nodes.length > MAX_DRAWN;
  ui.oversize.hidden = !oversize;
  ui.oversize.textContent = oversize
    ? `The net has ${next.nodes.length} nodes, too many to draw. Stepping still works.`
    : "";
  if (oversize) {
    animation += 1;
    positions = new Map();
    return;
  }

  const kinds = new Map(next.nodes.map((node) => [node.id, node.kind]));
  const pair = next.next ? new Set([next.next.upper, next.next.lower]) : new Set();
  const nodes = new Map(next.nodes.map((node) => [node.id, buildNode(node, pair.has(node.id))]));
  drawn.nodes = [...nodes.values()];
  drawn.wires = next.wires.map((wire) => {
    const isNext = wire.a_port === 0 && wire.b_port === 0 && pair.has(wire.a) && pair.has(wire.b);
    if (wire.a_port === 0) nodes.get(wire.a).faces = wire.b;
    if (wire.b_port === 0) nodes.get(wire.b).faces = wire.a;
    return { ...buildWire(wire, isNext), kindA: kinds.get(wire.a), kindB: kinds.get(wire.b) };
  });

  const targets = new Map(next.nodes.map((node) => [node.id, { x: node.column * COLUMN, y: node.row * ROW }]));
  const starts = new Map();
  for (const [id, target] of targets) starts.set(id, positions.get(id) ?? spawn ?? target);
  // Once the reader has zoomed or panned, the view stays where they put it.
  const viewTarget = following || !view ? boundsOf(targets.values()) : view;
  const viewStart = view ?? viewTarget;

  const token = ++animation;
  const length = animate ? duration() : 0;
  const began = performance.now();
  const tick = (now) => {
    if (token !== animation) return;
    // A frame's timestamp can predate `began`, hence the lower bound.
    const t = length > 0 ? Math.min(1, Math.max(0, (now - began) / length)) : 1;
    const e = ease(t);
    const at = new Map();
    for (const [id, target] of targets) {
      const start = starts.get(id);
      at.set(id, { x: mix(start.x, target.x, e), y: mix(start.y, target.y, e) });
    }
    positions = at;
    place(at);
    if (following || !view) {
      view = {
        x: mix(viewStart.x, viewTarget.x, e),
        y: mix(viewStart.y, viewTarget.y, e),
        w: mix(viewStart.w, viewTarget.w, e),
        h: mix(viewStart.h, viewTarget.h, e),
      };
      applyView();
    }
    if (t < 1) requestAnimationFrame(tick);
  };
  tick(began);
}

function applyView() {
  ui.net.setAttribute("viewBox", `${view.x} ${view.y} ${view.w} ${view.h}`);
}

// Zooms around the pointer: the point under it stays where it is.
function zoom(event) {
  if (!view) return;
  event.preventDefault();
  const pointer = new DOMPoint(event.clientX, event.clientY).matrixTransform(ui.net.getScreenCTM().inverse());
  const factor = Math.exp(event.deltaY * 0.0015);
  following = false;
  view = {
    x: pointer.x - (pointer.x - view.x) * factor,
    y: pointer.y - (pointer.y - view.y) * factor,
    w: view.w * factor,
    h: view.h * factor,
  };
  applyView();
}

let dragged = null; // where the pointer was, while it drags the net

function pan(event) {
  if (!dragged || !view) return;
  // The net is scaled to fit the canvas in both directions, so one screen
  // pixel is this many units of the viewBox.
  const scale = Math.max(view.w / ui.net.clientWidth, view.h / ui.net.clientHeight);
  following = false;
  view = {
    ...view,
    x: view.x - (event.clientX - dragged.x) * scale,
    y: view.y - (event.clientY - dragged.y) * scale,
  };
  dragged = { x: event.clientX, y: event.clientY };
  applyView();
}

function release() {
  dragged = null;
  ui.net.classList.remove("dragging");
}

function fit() {
  following = true;
  if (frame) draw(frame, true, null);
}

function readout() {
  ui.term.textContent = frame.term;
  const stats = frame.stats;
  ui.statBeta.textContent = stats.beta;
  ui.statBookkeeping.textContent = stats.annihilations + stats.commutations + stats.dissolutions;
  ui.statNodes.textContent = frame.nodes.length;
  ui.statCollected.textContent = stats.collected;
  if (frame.error) {
    ui.next.textContent = `Internal error: ${frame.error}`;
  } else if (frame.next) {
    const [name, text] = RULES[frame.next.rule];
    ui.next.replaceChildren(Object.assign(document.createElement("strong"), { textContent: name }), `: ${text}`);
  } else {
    ui.next.textContent = `Normal form reached after ${frame.step} interactions.`;
  }
  const done = !frame.next;
  for (const button of [ui.step, ui.beta, ui.play, ui.finish]) button.disabled = done;
  ui.back.disabled = !frame.can_go_back;
  ui.reset.disabled = !frame.can_go_back;
}

// ---------------------------------------------------------------- control

function problem(message) {
  ui.problem.hidden = !message;
  ui.problem.textContent = message ?? "";
}

function show(animate, spawn) {
  draw(JSON.parse(session.frame()), animate, spawn);
  readout();
}

// Where the pair that is about to interact sits, for new nodes to grow from.
function spawnPoint() {
  if (!frame?.next) return null;
  const upper = positions.get(frame.next.upper);
  const lower = positions.get(frame.next.lower);
  if (!upper || !lower) return null;
  return { x: (upper.x + lower.x) / 2, y: (upper.y + lower.y) / 2 };
}

// Fires steps while `more` allows it and returns the rule fired last.
function advance(more) {
  if (!session || !frame?.next) return null;
  const spawn = spawnPoint();
  let rule = null;
  let fired = 0;
  try {
    do {
      rule = session.step() ?? null;
      fired += 1;
    } while (rule && fired < MAX_BATCH && more(rule));
  } catch (error) {
    problem(String(error.message ?? error));
  }
  show(true, spawn);
  return rule;
}

function stop() {
  clearTimeout(timer);
  timer = null;
  ui.play.textContent = "Play";
}

function play() {
  if (timer !== null) return stop();
  ui.play.textContent = "Pause";
  const turn = () => {
    const rule = advance(() => false);
    if (rule && frame.next) timer = setTimeout(turn, duration() + 60);
    else stop();
  };
  timer = setTimeout(turn, 0);
}

function load() {
  stop();
  try {
    const loaded = new Session(ui.script.value);
    session?.free();
    session = loaded;
  } catch (error) {
    problem(String(error.message ?? error));
    return;
  }
  problem(null);
  positions = new Map();
  view = null;
  following = true;
  show(false, null);
}

function back() {
  stop();
  if (session?.back()) show(true, null);
}

function reset() {
  stop();
  if (!session) return;
  session.reset();
  show(true, null);
}

ui.load.addEventListener("click", load);
ui.step.addEventListener("click", () => (stop(), advance(() => false)));
ui.beta.addEventListener("click", () => (stop(), advance((rule) => rule !== "beta")));
ui.finish.addEventListener("click", () => (stop(), advance(() => true)));
ui.play.addEventListener("click", play);
ui.back.addEventListener("click", back);
ui.reset.addEventListener("click", reset);
ui.fit.addEventListener("click", fit);

ui.net.addEventListener("wheel", zoom, { passive: false });
ui.net.addEventListener("pointerdown", (event) => {
  dragged = { x: event.clientX, y: event.clientY };
  ui.net.setPointerCapture(event.pointerId);
  ui.net.classList.add("dragging");
});
ui.net.addEventListener("pointermove", pan);
ui.net.addEventListener("pointerup", release);
ui.net.addEventListener("pointercancel", release);

ui.examples.addEventListener("change", () => {
  ui.script.value = EXAMPLES[Number(ui.examples.value)][1];
  load();
});

document.addEventListener("keydown", (event) => {
  // Leave typing alone, and let space press whichever button has the focus.
  if (event.target.closest("textarea, select, input")) return;
  if (event.key === " " && event.target.closest("button")) return;
  const actions = { ArrowRight: () => ui.step.click(), ArrowLeft: back, " ": play, b: () => ui.beta.click(), f: fit };
  const action = actions[event.key];
  if (action) {
    event.preventDefault();
    action();
  }
});

ui.script.addEventListener("keydown", (event) => {
  if (event.key === "Enter" && (event.ctrlKey || event.metaKey)) load();
});

EXAMPLES.forEach(([name], index) => ui.examples.append(new Option(name, String(index))));
ui.script.value = EXAMPLES[0][1];

try {
  await init();
  load();
} catch (error) {
  problem(`The WebAssembly package did not load. Build it with scripts/build-web.sh.\n${error}`);
}
