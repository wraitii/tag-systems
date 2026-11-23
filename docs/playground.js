"use strict";

const byId = id => document.getElementById(id);
const preset = byId("preset");
const seed = byId("seed");
const assemblyInput = byId("assembly");
const linearInput = byId("linear");
const condensed = byId("condensed");
const fizzBlocks = fizzBuzzBlocks();
const loop = lowerMachine(distinguishJoins(readAssembly(LOOP_EXAMPLE)));
const zero = exampleLinear(0);
const positive = exampleLinear(1);
const bounce = bounceLinear();
const presets = {
  double: { word: W, blocks: [{ tile: W, copies: 1 }], target: 2, description: "Two sweeps turn one counter tile, W, into two." },
  fizz: { word: layoutWord(fizzBlocks), blocks: fizzBlocks, description: "Four clocks and one counter tile form the 2,128-symbol FizzBuzz seed." },
  zero: { ...compileLinear(zero), linear: writeLinear(zero), periods: 2, description: "The zero test succeeds, so each period increments Y." },
  positive: { ...compileLinear(positive), linear: writeLinear(positive), periods: 2, description: "The zero test fails, so Y stays at zero." },
  assembly: { ...compileLinear(loop), assembly: LOOP_EXAMPLE, linear: writeLinear(loop), description: "Test X, then increment Y and return to the test when X is positive." },
  bounce: { ...compileLinear(bounce), linear: writeLinear(bounce), implementation: "the edge compiler", periods: 5, description: "The machine increments X, reverses the increment, then returns to the same full queue." },
  get join() {
    const linear = lowerMachine(distinguishJoins(readAssembly(JOIN_EXAMPLE)));
    return {
      ...compileLinear(linear),
      assembly: JOIN_EXAMPLE,
      linear: writeLinear(linear),
      description: "Try starting X at 0 and at 1. Both runs halt at join with X = 1. Compare the history column in Period checkpoints to see which path arrived.",
    };
  },
};

const guardRegisters = [
  ["X", "Tested register. An underflow flips the cut for the next command."],
  ["Y", "Incremented once per period if X starts at zero."],
];
const bounceRegisters = [
  ["X", "Data register. Incremented forward and decremented on the return trip."],
  ["Forward s", "State flag. Zero marks this state as active."],
  ["Forward h", "State flag. Zero marks this state as active."],
  ["Backward s", "State flag. Zero marks this state as active."],
  ["Backward h", "State flag. Zero marks this state as active."],
  ["Increment latch", "Zero selects the forward edge that increments X."],
  ["Decrement latch", "Zero selects the backward edge that decrements X."],
  ["Turn at h latch", "Zero selects the turn from forward to backward."],
  ["Turn at s latch", "Zero selects the turn from backward to forward."],
];
const fizzClockRoles = [
  ["Fizz clock", "Sets the outgoing lane to the Fizz flag on the first sweep of each slot."],
  ["Buzz clock", "Applies Fizz XOR Buzz so the outgoing lane carries the Buzz flag."],
  ["Counter clock", "Removes the Buzz flag and selects the data lane. The padding slot includes a halving."],
  ["Closing clock", "Cancels the scheduled data-lane change so the next sweep starts with cut 0."],
];

const rules = new Map();
let machine, program, checkpoints, seen, cycle, stream, layout, cut, stopMessage;
let active = "double";
let busy = false;

function element(tag, text, className) {
  const node = document.createElement(tag);
  node.textContent = text;
  if (className) node.className = className;
  return node;
}

function symbolCell(char) {
  return element("span", char, `sym sym-${char}`);
}

function highlight(word) {
  return Array.from(word, symbolCell);
}

for (const [symbol, appendant] of Object.entries(RULES)) {
  const key = element("dt", symbol, `sym sym-${symbol}`);
  const value = element("dd", "→ ");
  value.append(...(appendant ? highlight(appendant) : ["ε"]));
  byId("rules").append(key, value);
  rules.set(symbol, key);
}

function captureCheckpoint() {
  const { period } = program;
  if (!period || machine.sweeps % period || cycle) return;
  const index = machine.sweeps / period;
  if (active === "assembly" || active === "join" || active === "custom") {
    checkpoints.push({ index, values: registerValues() });
    if (checkpoints.length > 8) checkpoints.shift();
    return;
  }
  const copies = layout.filter(({ block }) => !block.mask).map(({ block }) => block.copies);
  const values = copies.map(count => (Math.log2(count) - 4) / 4);
  const state = values.slice(1, 5).indexOf(0);
  checkpoints.push({
    index, x: values[0], y: values[1], xCopies: copies[0], yCopies: copies[1],
    direction: state < 2 ? "Forward" : "Backward",
    state: ["s", "h", "s", "h"][state],
  });
  if (checkpoints.length > 8) checkpoints.shift();
  if (active !== "bounce") return;
  const word = layoutWord(layout.map(({ block }) => block)).slice(cut);
  const previous = seen.get(word);
  if (previous !== undefined) {
    cycle = `Identical full queues at periods ${previous} and ${index} (${(index - previous) * period} sweeps apart).`;
  } else {
    seen.set(word, index);
  }
}

function renderCheckpoints() {
  const { period } = program;
  byId("checkpoints").hidden = !period;
  if (!period) return;
  const bounce = active === "bounce";
  const generic = active === "assembly" || active === "join" || active === "custom";
  byId("period-description").textContent = `${period} sweeps per period. W = ${W}.`;
  const table = element("table", "", generic ? "register-checkpoints" : "");
  const heading = table.createTHead().insertRow();
  const columns = generic ? ["Register", ...checkpoints.map(({ index }) => `Period ${index}`)]
    : bounce ? ["Period", "Direction", "State", "X", "X tiles"] : ["Period", "X", "Y", "X tiles", "Y tiles"];
  for (const name of columns) {
    const cell = element("th", name);
    cell.scope = "col";
    heading.append(cell);
  }
  const rows = generic
    ? program.registers.map(name => [name, ...checkpoints.map(({ values }) => values.get(name))])
    : checkpoints.map(({ index, x, y, xCopies, yCopies, direction, state }) => (
      bounce ? [index, direction, state, x, xCopies] : [index, x, y, xCopies, yCopies]
    ));
  const body = table.createTBody();
  for (const fields of rows) {
    const row = body.insertRow();
    for (const [i, value] of fields.entries()) {
      const cell = element(i ? "td" : "th", typeof value === "number" ? value.toLocaleString() : value, i ? "value" : "");
      if (i === 0) cell.scope = "row";
      row.append(cell);
    }
  }
  byId("checkpoint-table").replaceChildren(table);
  byId("cycle").hidden = !cycle;
  byId("cycle").textContent = cycle;
}

function diagramRole(isClock, i) {
  if (active === "fizz") {
    return isClock ? fizzClockRoles[i] : ["Output counter", "After output n, this run holds 4ⁿ copies of W."];
  }
  if (active === "double") return ["Counter block", "Two sweeps double the number of W tiles."];
  const registers = active === "bounce" ? bounceRegisters
    : active === "zero" || active === "positive" ? guardRegisters : null;
  const name = registers?.[i]?.[0] ?? program.registers[i];
  if (!isClock) return [name, registers?.[i]?.[1]];
  if (i === 0) return ["Entry clock", `Applies the scheduled lane for ${name}.`];
  if (i === program.registers.length) return ["Closing clock", "Cancels the last scheduled lane bit. A counter’s underflow still carries into the next cut."];
  return [`Clock before ${name}`, "XORs the previous and next scheduled lanes, passing through any underflow flip."];
}

function blockEncoding(block, width, logicalValue) {
  if (block.mask) {
    const count = block.mask.length;
    const code = element("code", `${count} D cells · ${count} I cells`);
    const odd = width - 8 * count;
    return [code, element("span", `${odd} odd cells · scheduled XOR ${block.mask[machine.sweeps % count]}`, "block-note")];
  }
  const tiles = block.copies === 1 ? "1 copy" : `${block.copies.toLocaleString()} copies`;
  const label = logicalValue === undefined ? tiles : `v = ${logicalValue} · ${tiles}`;
  return [runWord(block, logicalValue), element("span", label, "block-note")];
}

function runWord(block, logicalValue) {
  if (block.copies === 0) return element("code", "ε");
  const code = element("code", block.tile === W ? "W" : "b");
  const exponent = Math.log2(block.copies);
  if (block.copies > 1) {
    const binaryPower = Number.isInteger(exponent) && exponent > 1;
    const power = element("sup", binaryPower ? "2" : block.copies);
    if (binaryPower) {
      const display = logicalValue === undefined ? exponent : `4+4·${logicalValue}`;
      power.append(element("sup", display));
    }
    code.append(power);
  }
  return code;
}

function laneChip(lane) {
  return element("span", lane, `lane-chip lane-${lane}`);
}

function macroWord({ block, incoming, outgoing }, index, title, logicalValue) {
  const word = element("span", "", `macro-word lane-${incoming}`);
  if (incoming !== outgoing) word.classList.add("lane-flip");
  const encoding = block.mask ? element("code", "C") : runWord(block, logicalValue);
  if (block.mask) encoding.append(element("sub", index));
  const name = block.mask
    ? `Clock ${index}, ${title}`
    : `${title}, ${block.copies.toLocaleString()} copies of ${block.tile === W ? "W" : "b"}`;
  const value = logicalValue === undefined ? "" : ` Logical value ${logicalValue}.`;
  const label = `${name}.${value} Lane ${incoming} to ${outgoing}.`;
  word.setAttribute("role", "img");
  word.setAttribute("aria-label", label);
  word.title = label;
  word.append(encoding);
  return word;
}

function commandPhase(offset, period) {
  const command = Math.floor(offset / 2) + 1;
  const half = offset % 2 ? "return lane (b → W)" : "sign (W → b)";
  const stage = command <= 4 ? "Remove bias" : command <= 6 ? "First probe"
    : command <= 8 ? "Second probe" : command <= 12 ? "Restore bias" : "Padding";
  const guard = active === "zero" || active === "positive";
  return `Command ${command} of ${period / 2} · ${guard ? stage + " · " : ""}${half}`;
}

function renderDiagram() {
  condensed.disabled = !layout || busy;
  byId("diagram").hidden = !layout || !condensed.checked;
  byId("literal").hidden = Boolean(layout && condensed.checked);
  if (!layout || !condensed.checked) return;
  const end = layout.at(-1).outgoing;
  const heading = `Layout at the start of sweep ${machine.sweeps + 1}. Lane ${cut} enters and lane ${end} leaves.`;
  const boundary = end ? "The last deletion consumes the first appended symbol, so the next sweep starts at lane 1."
    : "The next sweep starts at lane 0.";
  byId("diagram-cut").textContent = `${heading} ${boundary}`;
  const { period, guards } = program;
  const offset = period ? machine.sweeps % period : 0;
  const command = byId("diagram-command");
  command.hidden = !period;
  const guard = guards?.[Math.floor(offset / 24)];
  const guardInfo = guard ? `Guard ${Math.floor(offset / 24) + 1} of ${guards.length} · ${guard.group || guard.comment || `Test ${guard.test} for zero`} · `
    : period && guards ? "Clock padding. " : "";
  command.textContent = period ? guardInfo + commandPhase(offset, period) : "";
  let clockIndex = 0;
  let dataIndex = 0;
  let scheduled = 0;
  const macroWords = [];
  const rows = layout.map(entry => {
    const { block, width, incoming, outgoing } = entry;
    const isClock = Boolean(block.mask);
    const index = isClock ? clockIndex++ : dataIndex++;
    const [title, role] = diagramRole(isClock, index);
    if (isClock && period) scheduled ^= block.mask[offset];
    const logicalValue = period && offset === 0 && !isClock ? (Math.log2(block.copies) - 4) / 4 : undefined;
    macroWords.push(macroWord(entry, index, title, logicalValue));
    const row = element("tr", "");
    const name = element("th", title, isClock ? "control" : "counter");
    name.scope = "row";
    if (role) name.append(element("span", role, "block-note"));
    const encoding = element("td", "", isClock ? "control" : "counter");
    encoding.append(...blockEncoding(block, width, logicalValue));
    if (period && !isClock) {
      const sign = lane => lane ? "decrement" : "increment";
      const note = offset % 2
        ? `Scheduled return lane ${scheduled} · actual lane ${incoming}`
        : `Scheduled ${sign(scheduled)} · actual ${sign(incoming)}`;
      encoding.append(element("span", note, "block-note"));
    }
    const lanes = element("td", "", "lanes");
    lanes.append(laneChip(incoming), " → ", laneChip(outgoing));
    if (incoming !== outgoing) lanes.append(element("span", "odd length", "block-note"));
    row.append(name, encoding, lanes);
    return row;
  });
  byId("macro-queue").replaceChildren(...macroWords);
  byId("diagram-blocks").replaceChildren(...rows);
}

function runTarget() {
  const { period, periods, target } = program;
  const goal = target ?? (period ? period * (periods ?? 1) : 0);
  if (machine.sweeps < goal) return { sweep: goal, label: `Run to sweep ${goal}` };
  if (period) {
    const next = Math.floor(machine.sweeps / period) + 1;
    return { sweep: next * period, label: "Run to next period" };
  }
  return { sweep: machine.sweeps + 4, label: "Run 4 sweeps" };
}

function render() {
  const { word, steps, sweeps, last } = machine;
  const { label } = runTarget();
  for (const [id, value] of [["steps", steps], ["sweeps", sweeps], ["length", word.length]]) {
    byId(id).textContent = value.toLocaleString();
  }
  const cells = word.length > 1024
    ? [...highlight(word.slice(0, 768)), element("span", `… ${(word.length - 1024).toLocaleString()} more …`, "tape-gap"), ...highlight(word.slice(-256))]
    : word ? highlight(word) : [element("span", "(empty)", "tape-gap")];
  if (word && !machine.stopped) {
    cells[0].classList.add("head");
    if (word.length > 1) cells[1].classList.add("head-pair");
  }
  byId("queue").replaceChildren(...cells);
  const next = machine.stopped ? "" : word[0];
  for (const [symbol, key] of rules) key.classList.toggle("active", symbol === next);
  const message = stopMessage || (word.length < 2 ? "Queue exhausted. A step needs two symbols."
    : word.length >= QUEUE_LIMIT ? "Literal queue reached the display runner’s size limit."
    : `Next ${word[0]} → ${RULES[word[0]] || "ε"} (delete ${word.slice(0, 2)}).`);
  byId("status").textContent = busy ? "Running sweeps…" : (last
    ? `Deleted ${last.deleted}, appended ${last.appended || "ε"}. ${message}` : message);
  byId("run").textContent = busy ? "Running…" : label;
  for (const id of ["step", "sweep", "run"]) byId(id).disabled = busy || machine.stopped || Boolean(stopMessage);
  for (const id of ["preset", "seed", "apply", "reset", "assembly", "linear", "assemble", "compile", "write-assembly", "write-linear"]) {
    byId(id).disabled = busy;
  }
  renderDiagram();
  renderCheckpoints();
}

function registerValues() {
  const data = layout.filter(({ block }) => !block.mask);
  return new Map(program.registers.map((name, i) => [name, (Math.log2(data[i].block.copies) - 4) / 4]));
}

function checkProgram() {
  const { period, guards, control } = program;
  if (!guards) return;
  const offset = machine.sweeps % period;
  if (offset % 24) return;
  const values = registerValues();
  if (offset === 0 && control) {
    const [state] = [...control.flags].find(([, flag]) => values.get(flag) === 0) ?? [];
    const enabled = control.edges.some(edge => {
      if (edge.source !== state) return false;
      const [test, register] = edgeTest(edge, false);
      return test === "N" || (test === "Z" ? values.get(register) === 0 : values.get(register) > 0);
    });
    if (control.terminal.has(state)) stopMessage = `Halt reached in state ${state} at period ${machine.sweeps / period}.`;
    else if (!enabled) stopMessage = `No enabled edge in state ${state}.`;
    if (stopMessage) return;
  }
  const index = offset / 24;
  const guard = guards[index];
  if (guard && values.get(guard.test) === 0) {
    const invalid = guard.updates.find(([name, delta]) => values.get(name) + delta < 0);
    if (invalid) stopMessage = `Guard ${index + 1} would decrement ${invalid[0]} below zero.`;
  }
}

function start(spec) {
  program = spec;
  machine = new TagQueue(spec.word);
  cut = 0;
  const { blocks } = spec;
  layout = blocks ? traceLayout(blocks, cut) : null;
  checkpoints = [];
  seen = new Map();
  cycle = "";
  stopMessage = "";
  stream = fizzBuzz();
  byId("description").textContent = spec.description;
  byId("fizz").hidden = active !== "fizz";
  byId("outputs").replaceChildren();
  byId("fizz-values").textContent = "";
  captureCheckpoint();
  checkProgram();
  render();
}

function inputError(id, message = "") {
  const error = byId(id);
  error.textContent = message;
  error.hidden = !message;
}

function showEditor(stage, show, implementation) {
  byId(`${stage}-editor`).hidden = !show;
  byId(`${stage}-missing`).hidden = show;
  if (!show) byId(`${stage}-implementation`).textContent = `(implemented directly in ${implementation})`;
}

function loadEdited(spec) {
  active = "custom";
  preset.value = active;
  start(spec);
}

function loadSource(fromAssembly) {
  const id = fromAssembly ? "assembly-error" : "linear-error";
  try {
    const linear = fromAssembly ? lowerMachine(distinguishJoins(readAssembly(assemblyInput.value))) : readLinear(linearInput.value);
    const spec = compileLinear(linear);
    if (fromAssembly) {
      linearInput.value = writeLinear(linear);
      showEditor("linear", true);
      inputError("linear-error");
    }
    seed.value = spec.word;
    inputError(id);
    inputError("error");
    loadEdited({ ...spec, description: fromAssembly ? "Running the assembled program." : "Running the linear guard schedule." });
  } catch (error) {
    inputError(id, error.message);
  }
}

function applyQueue() {
  const word = seed.value.replace(/\s/g, "");
  if (/[^IDzeab]/.test(word) || word.length >= QUEUE_LIMIT) {
    inputError("error", "Use only I, D, z, e, a, b and fewer than 2,000,000 symbols.");
    preset.value = active;
    return;
  }
  inputError("error");
  loadEdited({ word, description: "Running the literal queue." });
}

function advance(count) {
  const previous = machine.sweeps;
  machine.advance(count);
  if (machine.sweeps === previous) return;
  if (layout) advanceLayout();
  captureCheckpoint();
  checkProgram();
}

function advanceLayout() {
  cut = layout.at(-1).outgoing;
  layout = traceLayout(sweepLayout(layout), cut);
}

function runSweep() {
  if (!layout || machine.steps !== machine.sweepStart) {
    advance();
    return;
  }
  // A full sweep of a known layout is equivalent to the literal deletions.
  // Keep its banks and runs compressed until the next visible checkpoint.
  advanceLayout();
  machine.steps += machine.remaining;
  machine.last = null;
  machine.completeSweep(layout.reduce((sum, { width }) => sum + width, -cut));
  captureCheckpoint();
  checkProgram();
}

async function run() {
  const { sweep } = runTarget();
  busy = true;
  render();
  try {
    while (!machine.stopped && !stopMessage && machine.sweeps < sweep) {
      await new Promise(resolve => setTimeout(resolve, 0));
      const deadline = performance.now() + 16;
      do {
        runSweep();
      } while (!machine.stopped && !stopMessage && machine.sweeps < sweep && performance.now() < deadline);
    }
  } finally {
    if (layout && machine.steps === machine.sweepStart) {
      machine.word = layoutWord(layout.map(({ block }) => block)).slice(cut);
    }
    busy = false;
    render();
  }
}

function outputs(count) {
  const list = byId("outputs");
  let result;
  for (let i = 0; i < count; i++) {
    result = stream.next().value;
    const item = element("li", result.output);
    item.setAttribute("aria-label", `Output ${result.number}: ${result.output}`);
    list.append(item);
    if (list.children.length > 32) list.firstElementChild.remove();
  }
  const { number, exponent, sweeps, fizz, buzz } = result;
  const superscript = element("sup", exponent);
  byId("fizz-values").replaceChildren(
    `Output ${number} · ${sweeps} sweeps · `,
    element("span", `Fizz flag ${fizz} · Buzz flag ${buzz}`, "control"),
    " · ", element("span", "2", "value"), superscript, " copies of W",
  );
}

function loadPreset() {
  if (preset.value === "custom") {
    applyQueue();
    return;
  }
  active = preset.value;
  const spec = presets[active];
  assemblyInput.value = spec.assembly ?? "";
  linearInput.value = spec.linear ?? "";
  showEditor("assembly", Boolean(spec.assembly), spec.implementation ?? (spec.linear ? "linear guards" : "the literal queue"));
  showEditor("linear", Boolean(spec.linear), "the literal queue");
  seed.value = spec.word;
  for (const id of ["assembly-error", "linear-error", "error"]) inputError(id);
  start(spec);
}

preset.addEventListener("change", loadPreset);
for (const stage of ["assembly", "linear"]) {
  byId(`write-${stage}`).addEventListener("click", () => {
    showEditor(stage, true);
    byId(stage).focus();
  });
}
byId("assemble").addEventListener("click", () => loadSource(true));
byId("compile").addEventListener("click", () => loadSource(false));
byId("apply").addEventListener("click", applyQueue);
byId("reset").addEventListener("click", () => start(program));
condensed.addEventListener("change", renderDiagram);
byId("step").addEventListener("click", () => { advance(1); render(); });
byId("sweep").addEventListener("click", () => { advance(); render(); });
byId("run").addEventListener("click", run);
byId("next-output").addEventListener("click", () => outputs(1));
byId("next-16").addEventListener("click", () => outputs(16));
loadPreset();

window.openPresetInPlayground = name => {
  if (busy) return;
  preset.value = name;
  loadPreset();
};
