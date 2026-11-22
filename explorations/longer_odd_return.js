// Run with node longer_odd_return.js. Requires no dependencies.
'use strict';
const assert = require('node:assert/strict');

function countAs(word) {
  return word.length - word.replaceAll('a', '').length;
}

function table(a, b) {
  const rules = {a, b, z: 'e', e: ''};
  const nonUnary = {};
  for (const [letter, appendant] of Object.entries(rules)) {
    nonUnary[letter] = appendant.length - countAs(appendant);
  }
  return {rules, nonUnary};
}

// Check every deletion, including those strictly inside a sweep.
function firstReturn(system, n, maxSweeps, maxWidth) {
  let word = 'a'.repeat(n);
  let nonUnary = 0;
  for (let sweep = 1; sweep <= maxSweeps; sweep++) {
    if (word.length > maxWidth || word.length < 2) return null;
    const steps = Math.ceil(word.length / 2);
    let head = 0;
    for (let step = 0; step < steps; step++) {
      if (word.length - head < 2) return null;
      const first = word[head++];
      const second = word[head++];
      nonUnary -= Number(first !== 'a') + Number(second !== 'a');
      nonUnary += system.nonUnary[first];
      word += system.rules[first];
      if (nonUnary === 0) return {sweep, size: word.length - head};
    }
    word = word.slice(head);
  }
  return null;
}

function example() {
  const system = table('bbebezebez', 'a');
  for (let n = 2; n <= 256; n++) {
    let size = n / 2;
    let sweep = 2;
    if (n % 2) {
      let m = (n + 1) / 2;
      let d = 0;
      while (m % 2 === 0) {
        m /= 2;
        d++;
      }
      size = (3 ** (d + 1) * m + 1) / 2;
      sweep = 4 + 2*d;
    }
    assert.deepEqual(firstReturn(system, n, sweep, Infinity), {sweep, size});
  }
}

function wordsContaining(letter, maxLength) {
  let layer = [''];
  const results = [];
  for (let length = 1; length <= maxLength; length++) {
    const next = [];
    for (const prefix of layer) {
      for (const ch of 'abez') {
        const word = prefix + ch;
        next.push(word);
        if (word.includes(letter)) results.push(word);
      }
    }
    layer = next;
  }
  return results;
}

// A return from a mixed word to arbitrarily long all-a words requires a
// producer of a. We search the mutually producing a,b tables explicitly.
function searchLongerAppendant() {
  const groups = new Map();
  let tested = 0;
  const returns = ['a', 'aa', 'aaa', 'aaaa'];
  function visit(a) {
    if (a.includes('b')) {
      for (const b of returns) {
        tested++;
        const system = table(a, b);
        let pattern = new Set();
        let n = 2;
        for (; n <= 32; n++) {
          const yes = firstReturn(system, n, 8, 512);
          if (yes?.size !== (n % 2 ? (3*n + 1)/2 : n/2)) break;
          pattern.add((n % 2 ? 'odd' : 'even') + yes.sweep);
        }
        if (n > 32) {
          const key = [...pattern].sort().join('/');
          groups.set(key, (groups.get(key) || 0) + 1);
        }
      }
    }
    if (a.length < 10) for (const ch of 'abez') visit(a + ch);
  }
  visit('');
  console.log('Unary b productions, a appendant through length ten:', tested,
              'tested; matching first-return timings:', Object.fromEntries(groups));
}

function searchSmallTables() {
  const as = wordsContaining('b', 6);
  const bs = wordsContaining('a', 4);
  const hits = [];
  for (const a of as) {
    for (const b of bs) {
      const system = table(a, b);
      let n = 2;
      for (; n <= 32; n++) {
        const result = firstReturn(system, n, 8, 512);
        const target = n % 2 ? (3*n + 1)/2 : n/2;
        if (result?.size !== target) break;
      }
      if (n > 32) hits.push([a, b]);
    }
  }
  console.log('Tables tested:', as.length * bs.length);
  console.log('Survivors:', hits);
  assert.deepEqual(hits.map(pair => pair.join('/')).sort(),
    ['bbebeb/a', 'ebbbeb/a', 'ebebbb/a']);
}

example();
console.log('Verified first unary returns for the variable-delay example on inputs 2..256.');
searchSmallTables();
searchLongerAppendant();
