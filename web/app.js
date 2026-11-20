// The page: it hands scripts to the WebAssembly stepper and draws the frames
// that come back. All of the reduction logic lives on the Rust side.

const SVG = "http://www.w3.org/2000/svg";
const COLUMN = 62; // horizontal distance between neighbouring leaves
const ROW = 58; // vertical distance between a node and its children
const MARGIN = 44;
const MAX_DRAWN = 700; // nets with more nodes are not drawn
const SLICE = 12; // milliseconds a run works before it lets the page breathe

const RADIUS = { root: 4, lam: 15, app: 15, fan: 15, delim: 13, eraser: 8, free: 14 };

const RULES = {
  beta: ["β", "an application meets its abstraction. Both vanish, and two delimiters mark the scope the abstraction used to bind."],
  annihilate: ["Annihilate", "two fans or two delimiters of the same level meet and cancel out."],
  commute: ["Commute", "the two nodes pass through each other. Each is copied once per auxiliary port of the other."],
  dissolve: ["Dissolve", "a delimiter reaches the root or a free variable and vanishes."],
};

const EXAMPLES = [
  ["A shared redex", "-- The argument is used twice but reduced once.\n(\\x. f x x) ((\\y. y) a)\n"],
  ["Two applied to two", "two = \\f x. f (f x)\ntwo two\n"],
  ["Identity", "(\\x. x) y\n"],
  ["Erasure beats divergence", "-- The argument loops forever, but nothing needs it.\n(\\x. y) ((\\x. x x) (\\x. x x))\n"],
  ["Sharing under a binder", "-- Copying the abstraction must not copy the redex inside it.\n(\\f. f (f a)) (\\x. (\\y. y) x)\n"],
  ["Lamping's example", "(\\g. g (g (\\x. x))) (\\h. (\\f. f (f (\\z. z))) (\\w. h (w (\\y. y))))\n"],
  ["An abstraction inside its own copy", "\\x. (\\f. f f) (\\g. x (\\y. g y))\n"],
  ["Exponentiation", "-- 2 ^ (2 ^ 2), then applied to two identities.\n2 2 2 (\\x. x) (\\x. x)\n"],
  ["Factorial of two", "-- `fact` comes from the prelude, as do `eq`, `pair`, `fib` and the rest.\nfact 2\n"],
];

const $ = (id) => document.getElementById(id);
const ui = {
  examples: $("examples"),
  script: $("script"),
  scriptColors: $("script-colors"),
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

let Session = null; // the class of the stepper, once the package is loaded
let restarts = 0; // how many times the package had to be loaded again
let session = null;
let frame = null; // the frame on screen
let drawn = { nodes: [], wires: [] }; // its SVG elements
let positions = new Map(); // node id -> where it is drawn right now
let view = null; // the viewBox right now
let home = null; // the viewBox that shows the whole net
let following = true; // whether the view keeps the whole net in sight
let animation = 0; // identifies the running animation; bumping it cancels
let timer = null; // set while playing or running
let run = null; // the button that started the run under way, and its label

const calm = window.matchMedia("(prefers-reduced-motion: reduce)");

function svg(name, attributes, parent) {
  const element = document.createElementNS(SVG, name);
  for (const [key, value] of Object.entries(attributes)) element.setAttribute(key, value);
  parent?.append(element);
  return element;
}

// ---------------------------------------------------------------- colors

// The tokens of the language, as the parser reads them. A name never holds
// a λ, which always starts an abstraction.
const TOKEN = /(--[^\n]*)|([λ\\])|(\d+)|((?:(?!λ)[\p{L}_])(?:(?!λ)[\p{L}\p{N}_'])*)|(=)|([().])|(\s+|.)/gu;
const DEFINES = /[ \t]*=/y;

function span(kind, text) {
  return Object.assign(document.createElement("span"), { className: `t-${kind}`, textContent: text });
}

// Fills `element` with `text`, each token in a span classed for its color.
function colorize(element, text) {
  const parts = [];
  let plain = "";
  const add = (kind, token) => {
    if (plain) parts.push(plain);
    plain = "";
    parts.push(span(kind, token));
  };
  for (const match of text.matchAll(TOKEN)) {
    const [token, comment, lambda, number, name, equals, punctuation] = match;
    const end = match.index + token.length;
    if (comment) add("comment", token);
    else if (lambda) add("keyword", token);
    else if (number) add("number", token);
    else if (name && (match.index === 0 || text[match.index - 1] === "\n") && defines(text, end)) {
      // The name a definition defines starts its line.
      add("definition", token);
    } else if (equals) add("operator", token);
    else if (punctuation) add("punctuation", token);
    else plain += token;
  }
  if (plain) parts.push(plain);
  element.replaceChildren(...parts);
}

function defines(text, at) {
  DEFINES.lastIndex = at;
  return DEFINES.test(text);
}

// Shows the colors of the script under its transparent text.
function paintScript() {
  const text = ui.script.value;
  // A last empty line needs something in it to take up its height.
  colorize(ui.scriptColors, text.endsWith("\n") ? `${text} ` : text);
  ui.scriptColors.scrollTop = ui.script.scrollTop;
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
      return node.height > 1
        ? `${node.height} stacked delimiters, level ${node.level}`
        : `delimiter, level ${node.level}`;
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
  if (node.height > 1) svg("text", { class: "height", x: 16, y: 9 }, group).textContent = `×${node.height}`;
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

  const oversize = next.size > MAX_DRAWN;
  ui.oversize.hidden = !oversize;
  ui.oversize.textContent = oversize
    ? `The net has ${next.size} nodes, too many to draw. Stepping still works.`
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
  home = boundsOf(targets.values());
  const viewTarget = following || !view ? home : view;
  const viewStart = view ?? viewTarget;

  const token = ++animation;
  const length = animate && !calm.matches ? duration() : 0;
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

// Zooms around a point of the screen: what is under it stays where it is.
function zoomAt(clientX, clientY, factor) {
  if (!view) return;
  // From a few nodes across to a few times the whole net: beyond that there
  // is nothing to see, and the numbers of the viewBox run away.
  const widest = Math.max(home ? home.w * 8 : view.w, 4 * COLUMN);
  const width = Math.min(Math.max(view.w * factor, 2 * COLUMN), widest);
  const scale = width / view.w;
  const point = new DOMPoint(clientX, clientY).matrixTransform(ui.net.getScreenCTM().inverse());
  following = false;
  view = {
    x: point.x - (point.x - view.x) * scale,
    y: point.y - (point.y - view.y) * scale,
    w: view.w * scale,
    h: view.h * scale,
  };
  applyView();
}

function panBy(dx, dy) {
  if (!view) return;
  // The net is scaled to fit the canvas in both directions, so one screen
  // pixel is this many units of the viewBox.
  const scale = Math.max(view.w / ui.net.clientWidth, view.h / ui.net.clientHeight);
  following = false;
  view = { ...view, x: view.x - dx * scale, y: view.y - dy * scale };
  applyView();
}

const pointers = new Map(); // where each pointer that is down on the net was
let pinch = null; // how far apart two of them were, and the point between

function press(event) {
  if (event.pointerType === "mouse" && event.button !== 0) return;
  pointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
  pinch = null;
  ui.net.setPointerCapture(event.pointerId);
  ui.net.classList.add("dragging");
}

function drag(event) {
  const last = pointers.get(event.pointerId);
  if (!last) return;
  // A button let go outside the window never says so.
  if (event.pointerType === "mouse" && event.buttons === 0) return release(event);
  const here = { x: event.clientX, y: event.clientY };
  pointers.set(event.pointerId, here);
  if (pointers.size === 1) return panBy(here.x - last.x, here.y - last.y);
  if (pointers.size !== 2) return;
  // Two fingers: the point between them drags, their distance zooms.
  const [a, b] = [...pointers.values()];
  const now = { span: Math.hypot(a.x - b.x, a.y - b.y), x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
  if (pinch) {
    panBy(now.x - pinch.x, now.y - pinch.y);
    if (now.span > 0 && pinch.span > 0) zoomAt(now.x, now.y, pinch.span / now.span);
  }
  pinch = now;
}

function release(event) {
  pointers.delete(event.pointerId);
  pinch = null;
  if (pointers.size === 0) ui.net.classList.remove("dragging");
}

function fit() {
  following = true;
  if (frame) draw(frame, true, null);
}

function readout() {
  // A term too large to show comes as a note in angle brackets.
  if (frame.term.startsWith("<")) ui.term.replaceChildren(span("comment", frame.term));
  else colorize(ui.term, frame.term);
  const stats = frame.stats;
  ui.statBeta.textContent = stats.beta;
  ui.statBookkeeping.textContent = stats.annihilations + stats.commutations + stats.dissolutions;
  ui.statNodes.textContent = frame.size;
  ui.statCollected.textContent = stats.collected;
  if (frame.error) {
    ui.next.textContent = `Internal error: ${frame.error}`;
  } else if (frame.next) {
    const [name, text] = RULES[frame.next.rule];
    ui.next.replaceChildren(Object.assign(document.createElement("strong"), { textContent: name }), `: ${text}`);
  } else if (frame.normal) {
    ui.next.textContent = `Normal form reached after ${frame.step} interactions.`;
  } else {
    // The stepper looks only so far for the next interaction.
    ui.next.textContent = `Stopped after ${frame.step} interactions: the term is too large to read on to the next one, or to its end.`;
  }
  const done = !frame.next;
  for (const button of [ui.step, ui.beta, ui.play, ui.finish]) button.disabled = done;
  ui.back.disabled = !frame.can_go_back;
  // The start can always be gone back to, even when the steps cannot.
  ui.reset.disabled = frame.step === 0;
}

// ---------------------------------------------------------------- control

function problem(message) {
  ui.problem.hidden = !message;
  ui.problem.textContent = message ?? "";
}

// Loads the WebAssembly package. Every call gives a fresh instance with a
// memory of its own, which is how the page gets over one that broke down.
async function boot() {
  const again = restarts ? `?restart=${restarts}` : "";
  const module = await import(`./pkg/levy_web.js${again}`);
  await module.default();
  Session = module.Session;
}

const FAILED = Symbol("failed");

// A trap inside WebAssembly, which is what running out of memory looks like,
// leaves the instance unusable: its objects stay locked for good.
function isBreakdown(error) {
  const text = String(error?.message ?? error);
  return (
    error instanceof WebAssembly.RuntimeError ||
    error instanceof RangeError ||
    /unreachable|out of memory|null pointer passed to rust|recursive use of an object/i.test(text)
  );
}

// Nothing can be stepped until a script is loaded again.
function idle() {
  for (const button of [ui.reset, ui.back, ui.step, ui.beta, ui.play, ui.finish]) button.disabled = true;
}

async function recover(error) {
  // The session goes first: ending a run shows the frame of the one there
  // is, and asking a broken one for it would bring the page back here.
  session = null;
  Session = null;
  frame = null;
  stop();
  restarts += 1;
  idle();
  ui.next.textContent = "";
  const what = `The reducer broke down on this term, most likely for lack of memory (${error?.message ?? error}).`;
  problem(`${what} Restarting it…`);
  try {
    await boot();
    problem(`${what} It was restarted: load another script to go on.`);
  } catch (failure) {
    problem(`${what} It could not be restarted: reload the page.\n${failure}`);
  }
}

// Calls into the stepper. If the call fails, says why and returns FAILED.
function attempt(call) {
  try {
    return call();
  } catch (error) {
    if (isBreakdown(error)) recover(error);
    else problem(String(error?.message ?? error));
    return FAILED;
  }
}

function show(animate, spawn) {
  if (!session) return;
  const json = attempt(() => session.frame(MAX_DRAWN));
  if (json === FAILED) return;
  draw(JSON.parse(json), animate, spawn);
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

// Fires one interaction and returns its rule, or null if there was none.
function step() {
  if (!session || !frame?.next) return null;
  const spawn = spawnPoint();
  const rule = attempt(() => session.step() ?? null);
  if (rule === FAILED) return null;
  show(true, spawn);
  return rule;
}

// Ends whatever is playing or running.
function stop() {
  clearTimeout(timer);
  timer = null;
  ui.play.textContent = "Play";
  if (!run) return;
  // A run draws nothing until it ends, so the screen is behind.
  run.button.textContent = run.label;
  run = null;
  show(false, null);
}

function play() {
  if (timer !== null) return stop();
  ui.play.textContent = "Pause";
  const turn = () => {
    const rule = step();
    if (rule && frame?.next) timer = setTimeout(turn, duration() + 60);
    else stop();
  };
  timer = setTimeout(turn, 0);
}

// Runs to the normal form, or to the next β-step, in slices of a few
// milliseconds so that the page stays alive and the run can be stopped.
function runFrom(button, untilBeta) {
  const running = run?.button === button;
  stop();
  if (running || !session || !frame?.next) return;
  const spawn = spawnPoint();
  run = { button, label: button.textContent };
  button.textContent = "Stop";
  let interactions = 64; // per slice, adjusted to what the net allows
  const turn = () => {
    const began = performance.now();
    const rule = attempt(() => session.run(interactions, untilBeta) ?? null);
    if (rule === FAILED) return stop();
    if (rule === null || (untilBeta && rule === "beta")) {
      run.button.textContent = run.label;
      run = null;
      timer = null;
      return show(true, spawn);
    }
    const took = performance.now() - began;
    if (took < SLICE / 2) interactions = Math.min(interactions * 2, 1 << 24);
    else if (took > SLICE * 2) interactions = Math.max(1, interactions >> 1);
    ui.next.textContent = `Running: ${session.steps()} interactions so far.`;
    timer = setTimeout(turn, 0);
  };
  timer = setTimeout(turn, 0);
}

function load() {
  stop();
  if (!Session) return;
  const loaded = attempt(() => new Session(ui.script.value));
  if (loaded === FAILED) return;
  // The old session goes only now that the new one is there.
  try {
    session?.free();
  } catch {
    // It is lost either way.
  }
  session = loaded;
  problem(null);
  positions = new Map();
  view = null;
  following = true;
  show(false, null);
}

function back() {
  stop();
  if (!session) return;
  const undone = attempt(() => session.back());
  if (undone === true) show(true, null);
}

function reset() {
  stop();
  if (!session) return;
  if (attempt(() => session.reset()) !== FAILED) show(true, null);
}

ui.load.addEventListener("click", load);
ui.step.addEventListener("click", () => (stop(), step()));
ui.beta.addEventListener("click", () => runFrom(ui.beta, true));
ui.finish.addEventListener("click", () => runFrom(ui.finish, false));
ui.play.addEventListener("click", play);
ui.back.addEventListener("click", back);
ui.reset.addEventListener("click", reset);
ui.fit.addEventListener("click", fit);

// A button pressed with the mouse should not keep the keyboard: space would
// press it again instead of playing. Pressed from the keyboard, it keeps it.
document.addEventListener("click", (event) => {
  if (event.detail > 0) event.target.closest?.("button")?.blur();
});

ui.net.addEventListener("wheel", (event) => {
  event.preventDefault();
  zoomAt(event.clientX, event.clientY, Math.exp(event.deltaY * 0.0015));
}, { passive: false });
ui.net.addEventListener("pointerdown", press);
ui.net.addEventListener("pointermove", drag);
ui.net.addEventListener("pointerup", release);
ui.net.addEventListener("pointercancel", release);

ui.examples.addEventListener("change", () => {
  ui.script.value = EXAMPLES[Number(ui.examples.value)][1];
  paintScript();
  // The arrow keys go back to stepping, not to the list of examples.
  ui.examples.blur();
  load();
});
ui.speed.addEventListener("change", () => ui.speed.blur());

document.addEventListener("keydown", (event) => {
  // The shortcuts are plain keys. With a modifier, a key is the browser's.
  if (event.ctrlKey || event.metaKey || event.altKey) return;
  // Leave typing alone, and let space press whichever button has the focus.
  if (event.target.closest("textarea, select, input")) return;
  const key = event.key.length === 1 ? event.key.toLowerCase() : event.key;
  if (key === " " && event.target.closest("button")) return;
  const actions = {
    ArrowRight: () => ui.step.click(),
    ArrowLeft: back,
    " ": play,
    b: () => ui.beta.click(),
    f: fit,
  };
  const action = actions[key];
  if (!action) return;
  event.preventDefault();
  // A key held down steps on and on, but toggles nothing.
  if (event.repeat && !key.startsWith("Arrow")) return;
  action();
});

ui.script.addEventListener("keydown", (event) => {
  if (event.key === "Enter" && (event.ctrlKey || event.metaKey)) load();
});
ui.script.addEventListener("input", paintScript);
ui.script.addEventListener("scroll", () => (ui.scriptColors.scrollTop = ui.script.scrollTop));

EXAMPLES.forEach(([name], index) => ui.examples.append(new Option(name, String(index))));
ui.script.value = EXAMPLES[0][1];
paintScript();
idle();

try {
  await boot();
  load();
} catch (error) {
  problem(`The WebAssembly package did not load. Build it with scripts/build-web.sh.\n${error}`);
}
