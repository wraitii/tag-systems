"use strict";

const IDENTIFIER = "[A-Za-z_][A-Za-z_0-9]*";
const declarationPattern = new RegExp(`^reg\\s+(${IDENTIFIER})\\s*=\\s*(\\d+)$`, "i");
const labelPattern = new RegExp(`^(${IDENTIFIER}):$`);
const guardPattern = new RegExp(`^if\\s+(${IDENTIFIER})\\s*==\\s*0\\s*:\\s*(.+)$`, "i");
const changePattern = new RegExp(`^(${IDENTIFIER})\\s*(\\+=|-=)\\s*1$`);
const branchPattern = new RegExp(`^if\\s+(?:\\(\\s*)?(${IDENTIFIER})\\s*(==|>)\\s*0(?:\\s*\\))?\\s+goto\\s+(${IDENTIFIER})\\s+(?:else\\s+)?goto\\s+(${IDENTIFIER})$`, "i");
const actionPattern = new RegExp(`^(inc|dec)\\s+(${IDENTIFIER})(?:\\s+|$)`, "i");
const gotoPattern = new RegExp(`^goto\\s+(${IDENTIFIER})$`, "i");

const LOOP_EXAMPLE = `reg X = 1
reg Y = 0

start:
  if X == 0 goto halt
  goto add_y

add_y:
  inc Y
  goto start

halt:
  halt`;

const JOIN_EXAMPLE = `reg X = 0

start:
  if X == 0 goto left
  goto right

left:
  inc X
  goto join

right:
  goto join

join:
  halt`;

function readSource(source, readStatement) {
  const registers = new Map();
  source.split(/\r?\n/).forEach((line, i) => {
    const [statement, ...comment] = line.split("#");
    const text = statement.trim();
    const lineError = message => { throw new Error(`Line ${i + 1}. ${message}`); };
    const declaration = text.match(declarationPattern);
    if (declaration) {
      const [, name, value] = declaration;
      if (registers.has(name)) lineError(`Register ${name} is already declared.`);
      if (!Number.isSafeInteger(Number(value))) lineError("Use a nonnegative integer as the initial value.");
      registers.set(name, Number(value));
    } else {
      readStatement(text, comment.join("#").trim(), lineError);
    }
  });
  return registers;
}

function edgeTest({ op, register }, reverse) {
  if (op === "Z" || op === "P") return [op, register];
  if ((!reverse && op === "-") || (reverse && op === "+")) return ["P", register];
  return ["N", register];
}

function allocateName(names, prefix) {
  let name = prefix;
  while (names.has(name)) name = "_" + name;
  names.add(name);
  return name;
}

function readAssembly(source) {
  const states = new Map();
  let current;
  const data = readSource(source, (text, _, error) => {
    if (!text) return;
    const label = text.match(labelPattern);
    if (label) {
      current = label[1];
      if (states.has(current)) error(`State ${current} is already declared.`);
      states.set(current, { statements: [], error });
    } else {
      if (!current) error("Put instructions below a state label, such as start:.");
      states.get(current).statements.push(text);
    }
  });

  if (!states.size) throw new Error("Declare at least one labelled state.");
  const names = new Set(states.keys());
  const edges = [];
  const terminal = [];
  for (const [state, { statements, error }] of states) {
    let body = statements.join(" ").replace(/;/g, " ").trim();
    let from = state;
    let step = 1;
    function add(op, register, destination, instruction) {
      if (register && !data.has(register)) error(`Unknown register ${register}.`);
      edges.push({ source: from, op, register, destination, instruction });
    }
    function target(name) {
      if (!states.has(name)) error(`Unknown destination ${name}.`);
      return name;
    }
    let action;
    while ((action = body.match(actionPattern))) {
      const [matched, mnemonic, register] = action;
      body = body.slice(matched.length);
      const jump = body.match(gotoPattern);
      const destination = jump ? target(jump[1]) : allocateName(names, `${state}_${++step}`);
      add(mnemonic.toLowerCase() === "inc" ? "+" : "-", register, destination, `${mnemonic} ${register}`);
      from = destination;
      if (jump) {
        body = "";
        break;
      }
    }
    const branch = body.match(branchPattern);
    const jump = body.match(gotoPattern);
    if (/^halt$/i.test(body)) {
      terminal.push(from);
    } else if (branch) {
      const [, register, comparison, yes, no] = branch;
      const zero = comparison === "==";
      add(zero ? "Z" : "P", register, target(yes), `if ${register} ${comparison} 0`);
      add(zero ? "P" : "Z", register, target(no), "else");
    } else if (jump) {
      add("N", undefined, target(jump[1]), body);
    } else if (body || !action) {
      error("End each block with a conditional goto and fallback, a goto, or halt.");
    }
  }
  return { data, states: [...names], edges, terminal };
}

function distinguishJoins(machine) {
  const incoming = new Map();
  for (const edge of machine.edges) {
    if (!incoming.has(edge.destination)) incoming.set(edge.destination, []);
    incoming.get(edge.destination).push(edge);
  }
  function ambiguous(group) {
    if (group.length !== 2) return group.length > 2;
    const [[left, x], [right, y]] = group.map(edge => edgeTest(edge, true));
    return left === "N" || right === "N" || left === right || x !== y;
  }
  const joins = [...incoming].filter(([, group]) => ambiguous(group));
  if (!joins.length) return machine;

  const data = new Map(machine.data);
  const registers = new Set(data.keys());
  const history = allocateName(registers, "history");
  const work = allocateName(registers, "history_work");
  data.set(history, 0);
  data.set(work, 0);
  const states = new Set(machine.states);
  const redirects = new Map();
  const extra = [];
  const state = name => allocateName(states, name);
  function add(source, op, register, destination, instruction, historyRecorded = false) {
    extra.push({ source, op, register, destination, instruction, historyRecorded });
  }

  // Adapt the history/work loop in lean/ReversibleCounter.lean to each
  // ambiguous join. Incoming edge i pushes digit width - i in base width.
  for (const [destination, group] of joins) {
    const phase = group.map((_, i) => state(`${destination}_history_${i + 1}`));
    const top = state(`${destination}_history_loop`);
    const again = state(`${destination}_history_again`);
    add(top, "Z", work, destination, "History recorded", true);
    add(top, "-", work, again, "Take one old history unit from work");
    add(again, "P", history, phase[0], "Append a full set of history units");
    group.forEach((edge, i) => {
      const entry = state(`${destination}_incoming_${i + 1}`);
      const transfer = state(`${entry}_transfer`);
      const increment = state(`${entry}_save`);
      redirects.set(edge, { ...edge, destination: entry, originalDestination: destination });
      add(entry, "Z", work, transfer, `Record arrival at ${destination} from ${edge.source}`);
      add(transfer, "Z", history, phase[i], "Start the incoming edge’s history digit");
      add(transfer, "-", history, increment, "Move old history to work");
      add(increment, "+", work, transfer, "Save one old history unit");
      const next = phase[i + 1];
      const append = next ? state(`${phase[i]}_append`) : top;
      add(phase[i], "+", history, append, "Append one history unit");
      if (next) add(append, "P", history, next, "Continue appending history");
    });
  }
  const edges = [...machine.edges.map(edge => redirects.get(edge) ?? edge), ...extra];
  return { ...machine, data, states: [...states], edges };
}

// The select, execute and clear phases of examples/parity_program.py.
function lowerMachine({ data, states, edges, terminal = [] }) {
  const registers = new Map(data);
  const names = new Set(registers.keys());
  function allocate(prefix, value) {
    const name = allocateName(names, prefix);
    registers.set(name, value);
    return name;
  }
  const flags = new Map(states.map((state, index) => [state, allocate(`state_${state}`, Number(index !== 0))]));
  const latches = edges.map((_, index) => allocate(`edge_${index + 1}`, 1));
  const constant = edges.some(edge => edge.op === "Z") ? allocate("const_zero", 0) : null;
  const incomingCount = new Map();
  for (const { destination } of edges) {
    incomingCount.set(destination, (incomingCount.get(destination) ?? 0) + 1);
  }
  const guards = [];

  function add(test, changes, phase, group) {
    const combined = new Map();
    for (const [name, delta] of changes) combined.set(name, (combined.get(name) ?? 0) + delta);
    const updates = [...combined].filter(([, delta]) => delta !== 0);
    if (updates.length) guards.push({ test, updates, phase, group });
  }

  function transition(edge) {
    if (edge.originalDestination) {
      return `${edge.source} → ${edge.originalDestination} via ${edge.destination}`;
    }
    return `${edge.source} → ${edge.destination}`;
  }

  function select(edge, latch, reverse) {
    const block = reverse ? edge.destination : edge.source;
    const flag = flags.get(block);
    // Each live assembled period takes one edge. A sole incoming edge
    // is therefore identified by the destination flag alone.
    const uniqueArrival = reverse && incomingCount.get(block) === 1;
    const [test, register] = uniqueArrival ? ["N"] : edgeTest(edge, reverse);
    const condition = test === "N" ? "" : `${register} ${test === "Z" ? "==" : ">"} 0`;
    const phase = reverse ? "clear" : "select";
    const path = transition(edge);
    const reason = edge.historyRecorded ? "The history register records the original incoming edge."
      : uniqueArrival ? "Only one incoming edge, so the state is enough."
      : `On entry, ${condition} identifies which edge was taken.`;
    const group = reverse
      ? `At state ${block}, clear the entry latch for ${path}. ${reason}`
      : `At ${block}, ${condition ? `if ${condition} then ` : ""}take the ${path} edge.`;
    const offset = test === "Z" ? [[constant, 1], [register, -1]]
      : test === "P" ? [[register, 1]] : [];
    for (const [guard, delta] of offset) add(guard, [[flag, delta]], phase, group);
    add(flag, [[latch, reverse ? 1 : -1]], phase, group);
    for (const [guard, delta] of offset.reverse()) add(guard, [[flag, -delta]], phase, group);
  }

  edges.forEach((edge, i) => select(edge, latches[i], false));
  edges.forEach((edge, i) => {
    const updates = [[flags.get(edge.source), 1], [flags.get(edge.destination), -1]];
    const modifies = edge.op === "+" || edge.op === "-";
    if (modifies) updates.push([edge.register, edge.op === "+" ? 1 : -1]);
    const action = modifies ? ` (${edge.instruction})` : "";
    add(latches[i], updates, "execute", `Take the ${transition(edge)} edge${action}.`);
  });
  edges.forEach((edge, i) => select(edge, latches[i], true));
  return { registers, guards, control: { flags, edges, terminal: new Set(terminal) } };
}

function writeLinear({ registers, guards, control }) {
  const declarations = [...registers].map(([name, value]) => `reg ${name} = ${value}`);
  const lines = [...declarations];
  const phases = control ? [
    ["select", "1. SELECT EDGES"],
    ["execute", "2. EXECUTE SELECTED EDGES"],
    ["clear", "3. CLEAR ENTRY LATCHES"],
  ] : [[undefined, ""]];
  for (const [phase, heading] of phases) {
    if (heading) lines.push("", `# === ${heading} ===`);
    let previous;
    for (const { test, updates, group, comment } of guards.filter(guard => guard.phase === phase)) {
      if (!group || group !== previous) lines.push("");
      if (group && group !== previous) lines.push(`# ${group}`);
      const changes = updates.map(([name, delta]) => `${name} ${delta > 0 ? "+=" : "-="} 1`).join(", ");
      lines.push(`if ${test} == 0: ${changes}${comment ? `  # ${comment}` : ""}`);
      previous = group;
    }
  }
  return lines.join("\n");
}

function readLinear(source) {
  const guards = [];
  let pendingComment = "";
  const registers = readSource(source, (text, comment, error) => {
    if (!text) {
      if (comment) pendingComment = comment;
      return;
    }
    const match = text.match(guardPattern);
    if (!match) error("Use if Register == 0: Other += 1, Third -= 1.");
    const [, test, changes] = match;
    const seen = new Set([test]);
    const updates = changes.split(",").map(change => {
      const parsed = change.trim().match(changePattern);
      if (!parsed) error("Each update must add or subtract 1.");
      const [, name, operator] = parsed;
      if (seen.has(name)) error(`The tested register and duplicate updates are disallowed (${name}).`);
      seen.add(name);
      return [name, operator === "+=" ? 1 : -1];
    });
    guards.push({ test, updates, comment: comment || pendingComment, error });
    pendingComment = "";
  });
  for (const { test, updates, error } of guards) {
    for (const name of [test, ...updates.map(([name]) => name)]) {
      if (!registers.has(name)) error(`Unknown register ${name}.`);
    }
  }
  return { registers, guards };
}

function compileLinear({ registers, guards, control }) {
  if (!registers.size) throw new Error("Declare at least one register.");
  const names = [...registers.keys()];
  const values = [...registers.values()];
  const period = clockPeriod(24 * guards.length);
  const minimum = 8 * ((names.length + 1) * period + values.reduce((sum, value) => sum + 2 ** (4 + 4 * value), 0));
  if (minimum >= QUEUE_LIMIT) throw new Error("The compiled queue is too large for the literal runner. Use fewer guards or smaller initial values.");
  const positions = new Map(names.map((name, i) => [name, i]));
  const rows = guards.flatMap(({ test, updates }) => {
    const changes = values.map(() => 0);
    for (const [name, delta] of updates) changes[positions.get(name)] = delta;
    return guarded(positions.get(test), changes);
  });
  const compiled = compile(rows, values);
  if (compiled.word.length >= QUEUE_LIMIT) throw new Error("The compiled queue exceeds the literal runner’s size limit.");
  return { ...compiled, registers: names, guards, control };
}

function exampleLinear(x) {
  return {
    registers: new Map([["X", x], ["Y", 0]]),
    guards: [{ test: "X", updates: [["Y", 1]], comment: "If X is zero, increment Y." }],
  };
}

function bounceLinear() {
  return lowerMachine({
    data: new Map([["X", 0]]),
    states: ["forward_s", "forward_h", "backward_s", "backward_h"],
    edges: [
      { source: "forward_s", destination: "forward_h", op: "+", register: "X", instruction: "inc X" },
      { source: "backward_h", destination: "backward_s", op: "-", register: "X", instruction: "dec X" },
      { source: "forward_h", destination: "backward_h", op: "N", instruction: "reverse at h" },
      { source: "backward_s", destination: "forward_s", op: "N", instruction: "reverse at s" },
    ],
  });
}
