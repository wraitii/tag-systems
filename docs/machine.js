"use strict";

const W = "aaaeaeae";
const RULES = Object.freeze({ I: "ezII", D: "DDez", z: "e", e: "", a: "b", b: W });
const QUEUE_LIMIT = 2_000_000;

class TagQueue {
  constructor(word) {
    this.word = word;
    this.size = word.length;
    this.steps = 0;
    this.sweepStart = 0;
    this.sweeps = 0;
    this.remaining = Math.ceil(word.length / 2);
    this.last = null;
  }

  get stopped() {
    return this.size < 2 || this.size >= QUEUE_LIMIT;
  }

  completeSweep(size) {
    this.size = size;
    this.sweeps++;
    this.sweepStart = this.steps;
    this.remaining = Math.ceil(size / 2);
  }

  // Finish at most one sweep. Its final pair can cross into the appended tail.
  advance(count = this.remaining) {
    if (this.stopped) return;
    count = Math.min(count, this.remaining);
    const word = this.word;
    const appended = [];
    let head = 0;
    let taken = 0;
    while (taken < count && head + 1 < word.length) {
      appended.push(RULES[word[head]]);
      head += 2;
      taken++;
    }

    let tail = appended.join("");
    if (taken < count && head === word.length - 1 && tail.length) {
      tail = tail.slice(1) + RULES[word[head]];
      head++;
      taken++;
    }

    this.last = taken === 1 ? { deleted: word.slice(0, 2), appended: RULES[word[0]] } : null;
    this.word = word.slice(head) + tail;
    this.size = this.word.length;
    this.steps += taken;
    this.remaining -= taken;
    if (this.remaining === 0) this.completeSweep(this.size);
  }
}

// Clock and guarded-update construction from examples/parity_program.py.
const bankShapes = new Map();

function bankShape(length) {
  if (bankShapes.has(length)) return bankShapes.get(length);
  const counts = [];
  const shifts = [];
  for (let stride = 1; stride < length; stride *= 2) {
    shifts.push(BigInt(stride));
    counts.push(BigInt("0b" + ("0".repeat(stride) + "1".repeat(stride)).repeat(length / (2 * stride))));
  }
  const high = 1n << BigInt(length - 1);
  const shape = { shifts, counts, high, all: 2n * high - 1n };
  bankShapes.set(length, shape);
  return shape;
}

function clock(mask) {
  const seed = mask.slice();
  for (let stride = 1; stride < seed.length; stride *= 2) {
    for (let i = 0; i < seed.length; i++) {
      if (!(i & stride)) seed[i] ^= seed[i | stride];
    }
  }
  const shape = bankShape(seed.length);
  return { mask, d: 0n, i: BigInt("0b" + seed.reverse().join("")), shape };
}

function clockWord({ mask, d, i }) {
  function bank(bits, even, odd) {
    const binary = bits.toString(2);
    const words = Array.from(binary).reverse().map(bit => bit === "1" ? odd : even);
    return words.join("") + even.repeat(mask.length - binary.length);
  }
  return bank(d, RULES.D, RULES.D + "e") + bank(i, RULES.I, "e" + RULES.I);
}

function population(bits, { shifts, counts }) {
  for (let i = 0; i < shifts.length; i++) {
    bits = (bits & counts[i]) + ((bits >> shifts[i]) & counts[i]);
  }
  return Number(bits);
}

function sweepClock(block, lane) {
  const { shape } = block;
  // Bit j corresponds to cell j, with the least significant bit at the front.
  function prefix(bits) {
    for (const shift of shape.shifts) bits ^= (bits << shift) & shape.all;
    return bits;
  }
  const d = prefix(block.d);
  const afterD = Boolean(d & shape.high) !== Boolean(lane);
  return {
    ...block,
    d: ((d << 1n) & shape.all) ^ (lane ? shape.all : 0n),
    i: prefix(block.i) ^ (afterD ? shape.all : 0n),
  };
}

function guarded(test, changes) {
  const rows = [];
  function emit(testSign, signs, probe = false) {
    rows.push(
      signs.map((sign, i) => Number((i === test ? testSign : sign) < 0)),
      signs.map((_, i) => Number(probe && i === test)),
    );
  }
  for (const sign of [1, -1, 1, -1]) emit(-1, changes.map(() => sign));
  for (const fallback of [1, -1]) {
    const signs = changes.map(change => change || fallback);
    emit(-1, signs);
    emit(1, signs.map(sign => -sign), true);
  }
  for (const sign of [1, -1, 1, -1]) emit(1, changes.map(() => sign));
  return rows;
}

function clockPeriod(sweeps) {
  return 2 ** Math.ceil(Math.log2(Math.max(4, sweeps)));
}

function compile(rows, values) {
  const period = clockPeriod(rows.length);
  const masks = Array.from({ length: values.length + 1 }, () => []);
  for (let sweep = 0; sweep < period; sweep++) {
    // Pad with balanced increment/decrement pairs, each followed by a zero mask.
    const lanes = rows[sweep] ?? values.map(() => Number(sweep % 4 === 2));
    let previous = 0;
    for (const [i, lane] of lanes.entries()) {
      masks[i].push(previous ^ lane);
      previous = lane;
    }
    masks[values.length].push(previous);
  }
  const blocks = [];
  for (const [i, mask] of masks.entries()) {
    blocks.push(clock(mask));
    if (i < values.length) blocks.push({ tile: W, copies: 2 ** (4 + 4 * values[i]) });
  }
  return { word: layoutWord(blocks), blocks, period };
}

function fizzBuzzBlocks() {
  const masks = [[], [], [], []];
  for (let slot = 1; slot <= 16; slot++) {
    const fizz = Number(slot % 3 === 0);
    const buzz = Number(slot % 5 === 0);
    const lane = Number(slot === 16);
    masks[0].push(fizz, 0, 0, 0);
    masks[1].push(fizz ^ buzz, 0, 0, 0);
    masks[2].push(buzz, 0, lane, 0);
    masks[3].push(0, 0, lane, 0);
  }
  const blocks = masks.map(clock);
  blocks.splice(3, 0, { tile: W, copies: 1 });
  return blocks;
}

function readLane(word, lane) {
  let output = "";
  for (let i = lane; i < word.length; i += 2) output += RULES[word[i]];
  return output;
}

function layoutWord(blocks) {
  return blocks.map(block => block.mask ? clockWord(block) : block.tile.repeat(block.copies)).join("");
}

// Nominal blocks retain the first symbol even when the physical cut removes it.
function traceLayout(blocks, cut) {
  let lane = cut;
  return blocks.map(block => {
    const incoming = lane;
    const width = block.mask ? 8 * block.mask.length + population(block.d, block.shape) + population(block.i, block.shape)
      : block.tile.length * block.copies;
    lane ^= width % 2;
    return { block, width, incoming, outgoing: lane };
  });
}

function sweepLayout(trace) {
  return trace.map(({ block, incoming }) => {
    if (block.mask) return sweepClock(block, incoming);
    return block.tile === W
      ? { tile: "b", copies: block.copies * (incoming === 0 ? 4 : 1) }
      : { tile: W, copies: Math.floor((block.copies + 1 - incoming) / 2) };
  });
}

// Same compressed physical sweep as examples/six_symbol_fizzbuzz.py.
function* fizzBuzz() {
  let clocks = fizzBuzzBlocks().filter(block => block.mask).map(clockWord);
  let tile = W;
  let exponent = 0;
  let sweeps = 0;
  let number = 0;
  while (true) {
    for (let slot = 1; slot <= 16; slot++) {
      let fizz, buzz;
      for (let tick = 0; tick < 4; tick++) {
        let lane = 0;
        clocks = clocks.map((block, i) => {
          if (i === 3) {
            exponent += tile === W ? Math.log2(readLane(tile, lane).length) : -1;
            tile = tile === W ? "b" : W;
          }
          const output = readLane(block, lane);
          lane ^= block.length % 2;
          if (tick === 0 && i === 0) fizz = lane;
          if (tick === 0 && i === 1) buzz = lane;
          return output;
        });
        sweeps++;
      }
      if (slot <= 15) {
        number++;
        const output = "Fizz".repeat(fizz) + "Buzz".repeat(buzz);
        yield { output: output || String(exponent / 2), number, exponent, sweeps, fizz, buzz };
      }
    }
  }
}
