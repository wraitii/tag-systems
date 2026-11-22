# A universal six-symbol 2-tag system

*Developed with GPT 6.2 Astra*

A 2-tag system reads the first letter of a queue, deletes the first two letters, and appends a fixed word for the letter read. Here is a fixed 6-symbol 2-tag system (`I D z e a b`, with `e → ε`):

```text
I → ezII       D → DDez       z → e
a → b          b → aaaeaeae   e → ε
```

These six rules are Turing-universal: any deterministic counter machine and input can be compiled into a single finite starting queue that eventually repeats identically if and only if the machine halts.

## What this achieves

- **Smallest known universal 2-tag system:** cuts the alphabet from 19 symbols ([UT19](https://esolangs.org/wiki/UT19), ais523, 2023) down to 6 symbols, with both program and data living inside a finite queue.
- **One of the smallest known universal machines:** just 6 productions and 18 output letters in total, with finite initial configurations (no infinite periodic background tape as in Rule 110). The trade-off is that halting is observed as *exact queue repetition* rather than queue exhaustion.
- **End-to-end verified in Lean 4:** [lean/SixSymbol.lean](lean/SixSymbol.lean) and [lean/ReversibleCounter.lean](lean/ReversibleCounter.lean) formally check the entire reduction from non-reversible deterministic counter machines, leaving only Minsky's universality theorem as an external premise.

For full proofs, algebraic derivations, and citations, see the paper ([PDF](paper/six-symbol-tag.pdf) / [LaTeX](paper/six-symbol-tag.tex)).

---

## The idea in 60 seconds

Deleting two letters per step means each pass over the queue (a *sweep*) reads only every second letter—either even positions (lane 0) or odd positions (lane 1). That 1-bit parity alignment acts as a control wire running down the queue:

1. **Program clocks (`I`, `D`, `z`, `e`):** Banks of differentiators (`DDez`/`DDeze`) followed by integrators (`ezII`/`eezII`) sit between counters and XOR a fixed periodic bitmask onto the passing lane without smearing earlier signals.
2. **Exponential counters (`a`, `b`):** A counter stores exponent $E$ as $2^E$ copies of $W = \texttt{aaaeaeae}$. Every two sweeps, lane 0 doubles it ($E \mapsto E+1$) and lane 1 halves it ($E \mapsto E-1$).
3. **Zero test via parity underflow:** Decrementing at $E = 0$ leaves a single odd-length `b`. Reading it regenerates $W$ while flipping the lane for the next command—letting a 12-command gadget branch on "counter = 0".
4. **Halting as exact repetition:** A reversible front end plus forward/backward "bouncing" copies trap halting runs in a bounded loop (forcing exact repetition), while divergent runs grow forever.

---

## Fun stuff you can run

### 1. Double a block by hand

Start with one copy of `W = aaaeaeae`. Each arrow is one literal 2-tag step:

```text
aaaeaeae → aeaeaeb → aeaebb → aebbb → bbbb
bbbb → bbaaaeaeae → aaaeaeaeaaaeaeae
```

Sweep 1 reads four `a`s (`bbbb`); sweep 2 reads two `b`s (`WW`).

### 2. FizzBuzz from a 2,128-letter queue

A single 2,128-letter starting queue runs FizzBuzz indefinitely. Run:

```sh
python3 -B examples/six_symbol_fizzbuzz.py
```

The first 16 outputs cross the first 64-sweep clock reset:

```text
1 2 Fizz 4 Buzz Fizz 7 8 Fizz Buzz 11 Fizz 13 14 FizzBuzz 16
```

- Each 64-sweep period has 15 emitting slots (4 sweeps each) plus 1 padding slot.
- Clocks 1 and 2 signal `Fizz` (slots 3, 6, 9, 12, 15) and `Buzz` (slots 5, 10, 15).
- The counter doubles twice per emitting slot, holding $4^n$ copies of `W` after output $n$ (decoded as $\log_4$ when neither flag fires).
- Use `--initial` to print the raw 2,128-letter queue or `--steps 3` to watch literal tag steps. See [examples/six_symbol_fizzbuzz.py](examples/six_symbol_fizzbuzz.py).

### 3. Zero-guarded counter

Compile *"if $X = 0$, increment $Y$"* and verify two full periods (32 sweeps each) against literal 2-tag execution (run with `PYTHONPATH=examples`):

```python
from parity_program import compile_program, guarded, verify

rows = guarded(0, [0, 1])  # Test X; on zero, add 1 to Y.
word, commands = compile_program(rows, [0, 0])
assert (len(word), len(commands)) == (1046, 16)
verify(rows, [0, 0], lambda n: [0, n], 2)  # Y grows: 16 → 256 → 4096 copies of W
verify(rows, [1, 0], lambda n: [1, 0], 2)  # Y stays at 16 copies
```

### 4. Increment once and bounce into an exact cycle

Give the compiler a single edge `s → h` that increments $X$. It builds the return trip automatically:

```python
from parity_program import bouncing_machine, compile_program

rows, values = bouncing_machine(["s", "h"], "s", "h", [0], [("s", "+", 0, "h")])
word, commands = compile_program(rows, values)
```

| Period | Direction | State | $X$ |
|---:|---|---|---:|
| 0 | Forward | `s` | 0 |
| 1 | Forward | `h` | 1 |
| 2 | Backward | `h` | 1 |
| 3 | Backward | `s` | 0 |
| 4 | Forward | `s` | 0 |
| 5 | Forward | `h` | 1 |

At checkpoints 1 and 5 (2,048 sweeps apart), the entire queues match identically, including every clock cell. Run `python3 -B examples/parity_program.py` to reproduce both checks.

---

## Rechecking the Lean 4 proof

The end-to-end theorem `ReversibleCounter.halt_iff_exact_cycle` proves:

```lean
(∃ n, (m.path input n).pc = m.halt) ↔
  ExactCycle (encode (rev m std.fresh) (liftInput input))
```

Recheck both files with Lean 4.19 (selected automatically via `lean-toolchain`):

```sh
lean lean/SixSymbol.lean
mkdir -p build
lean -o build/SixSymbol.olean lean/SixSymbol.lean
LEAN_PATH=build lean lean/ReversibleCounter.lean
```

Both main theorems depend only on standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx`.

---

## Is six minimal?

- **The 2-tag frontier is now 3, 4, and 5 symbols:** Binary (2-symbol) 2-tag systems are decidable (claimed by Post and proved by De Mol, 2010), while 3 symbols already reach Collatz dynamics via De Mol's (2008) system `a → bc`, `b → a`, `c → aaa`. Six symbols give universality, leaving 3, 4, and 5 as the open frontier.
- **For this clock architecture, six is tight:** [paper/clock_obstruction.tex](paper/clock_obstruction.tex) proves no three-letter closed clock alphabet (with an eraser) can implement both an integrator and a differentiator in one sweep, so $4 + 2 = 6$ is optimal here.
- **In general, open:** Dropping `D` gives a 5-symbol integrator-only compiler that matches any finite horizon, and a separate 5-symbol table in [explorations/five-symbol-tag.md](explorations/five-symbol-tag.md) explores reloading control directly from data.

---

## Repository layout

| Path | Description |
|---|---|
| [paper/six-symbol-tag.pdf](paper/six-symbol-tag.pdf) | Compiled paper with full proofs, constructions, and citations |
| [paper/six-symbol-tag.tex](paper/six-symbol-tag.tex) | LaTeX source of the paper |
| [paper/clock_obstruction.tex](paper/clock_obstruction.tex) | Standalone proof of the three-letter clock obstruction |
| [lean/SixSymbol.lean](lean/SixSymbol.lean) | Lean 4 proof of the reversible-machine-to-tag compiler |
| [lean/ReversibleCounter.lean](lean/ReversibleCounter.lean) | Lean 4 proof of the reversible front end and end-to-end theorem |
| [examples/parity_program.py](examples/parity_program.py) | Executable Python reference compiler and verifier |
| [examples/six_symbol_fizzbuzz.py](examples/six_symbol_fizzbuzz.py) | Runnable FizzBuzz 2-tag demo |
| [explorations/](explorations/) | Exploratory five-symbol, Collatz, and loop experiments |

---

<details>
<summary>Literal 2,128-letter FizzBuzz starting queue</summary>

```text
DDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIaaaeaeaeDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezII
```

</details>
