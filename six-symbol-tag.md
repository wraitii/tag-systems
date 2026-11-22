# A universal six-symbol 2-tag system with cycle detection

The alphabet is `I D z e a b`. Each tag step reads the first letter of the queue, deletes the first two letters, and appends the production assigned to the letter read (`e` appends the empty word $\varepsilon$). A queue shorter than two letters has no successor.

```text
I → ezII       D → DDez       z → e
a → b          b → aaaeaeae   e → ε
```

> **Main result.** There is a computable encoding of any deterministic counter machine (with a fresh entry, a terminal halt, and an enabled instruction at every nonhalting configuration; not necessarily reversible) and its input into a finite starting queue such that the machine halts if and only if the queue eventually repeats identically. Program and data live in the queue; the six productions are fixed. Lean 4 checks the entire reduction, leaving Minsky's universality theorem as the sole external premise.

---

## How it works

Because a 2-tag system deletes two letters per step, each pass over the queue (a **sweep**) reads only every second letter—either even positions (**lane 0**) or odd positions (**lane 1**). The construction turns this parity alignment into a 1-bit control wire running down the queue:

1. **Program clocks (`I`, `D`, `z`, `e`)** sit between counters and XOR a fixed, periodic bitmask onto the passing alignment without smearing earlier signals.
2. **Exponential counters (`a`, `b`)** store an exponent $E$ as $2^E$ copies of $W = \texttt{aaaeaeae}$, doubling on lane 0 ($E \mapsto E+1$) and halving on lane 1 ($E \mapsto E-1$) every two sweeps.
3. **Zero detection via underflow:** decrementing at $E = 0$ leaves a single odd-length `b`, flipping the alignment for the rest of the queue and feeding a zero-test bit into the next command.
4. **Cycle detection via reversibility:** we convert the source machine into a reversible one and bounce it between entry and halt—trapping halting runs in a bounded loop (forcing exact repetition) while divergent runs grow unboundedly.

---

## The program clock

### Sweeps and alignment

A sweep reads alternate letters of the queue. A block entered at alignment $p \in \{0, 1\}$ passes $p$ unchanged if its length is even and flips it to $p \oplus 1$ if its length is odd.

Represent the state as a **nominal word** (a concatenation of blocks) with a **cut bit** $p \in \{0, 1\}$; the physical queue is the nominal word minus its first $p$ letters:
- In a block $w$ entered on lane $u$, concatenate the productions at zero-based indices $u, u+2, \ldots$ to form the next block, and pass $u \oplus (|w| \bmod 2)$ to the next block.
- The outgoing lane at the end of the word becomes the next sweep's cut bit.

An even physical length ends cleanly on a two-letter deletion; an odd length leaves one old letter whose deletion also consumes the first newly appended letter, setting the next cut bit to 1. Because the leading clock always emits a full cell on either lane, this boundary crossing is always valid, and each sweep takes $\lceil |q|/2 \rceil$ literal tag steps.

### Clock cells: differentiators and integrators

Clocks are built from two 1-bit memory cells, each with an even-length **state 0** word and an odd-length **state 1** word:

| Cell | State 0 ($s=0$) | State 1 ($s=1$) | Outgoing lane $y$ | Next state $s'$ |
|---|---|---|---|---|
| Integrator | `ezII` | `eezII` | $p \oplus s$ | $p \oplus s$ |
| Differentiator | `DDez` | `DDeze` | $p \oplus s$ | $p$ |

Checking positions $0,2,\ldots$ (lane 0) and $1,3,\ldots$ (lane 1) confirms the table: `ezII` $\mapsto$ (`ezII`, `eezII`), `eezII` $\mapsto$ (`eezII`, `ezII`), and both `DDez` and `DDeze` $\mapsto$ (`DDez`, `DDeze`).

In both cells, width parity gives the outgoing bit $y = p \oplus s$. A differentiator therefore stores the previous input ($y_t = p_t \oplus p_{t-1}$), while an integrator stores the previous output ($y_t = p_t \oplus y_{t-1}$). Working over $\mathbb{F}_2[[X]]$—where $X$ delays a bit stream by one sweep—their zero-state input-output maps are:

- **Differentiator:** multiplication by $1 + X$
- **Integrator:** division by $1 + X$

Putting a bank of $L$ differentiators in front of $L$ integrators cancels their transfer functions on any incoming stream, leaving a block that passes arbitrary incoming parity straight through while XORing in a periodic mask determined by the integrators' initial seeds.

### Clock construction and seed formula

For a bitmask $m_0, \ldots, m_{L-1}$ whose period $L$ is a power of two, define the literal clock word $C(m)$ as:

1. $L$ copies of `DDez` (all differentiators initialized to 0), followed by
2. $L$ integrators for $i = 0, \ldots, L-1$, using `eezII` if seed bit $i$ is 1 and `ezII` if it is 0.

To compute seed bit $i$, XOR all $m_j$ for which the set bits of $i$ are a subset of the set bits of $j$:
$$
\mathrm{seed}_i = \bigoplus_{i \subseteq j} m_j.
$$

**Proof.** First set all seeds to zero; the $L$ differentiators and $L$ integrators cancel on every input stream. Now turn on seed $i$ alone. On zero input, cell $i$ emits the constant stream $1 + X + X^2 + \cdots = (1+X)^{-1}$, and $L - 1 - i$ integrators follow it. Its contribution to the output is:
$$
(1+X)^{-(L-i)} = \frac{(1+X)^i}{1 + X^L}.
$$
The denominator $1 + X^L$ repeats the numerator every $L$ sweeps. Factoring $(1+X)^i = \prod_{k \in \mathrm{bits}(i)} (1 + X^{2^k})$ over $\mathbb{F}_2$ shows that the numerator has a 1 at precisely the indices $t$ whose set bits are a subset of $i$'s. Thus the output at sweep $t < L$ XORs the seeds over all supersets $i \supseteq t$.

Applying this superset-XOR transform twice counts each superset $j \supseteq t$ once for every intermediate subset $i$ with $t \subseteq i \subseteq j$. That count is $2^{|j \setminus t|}$, which is odd if and only if $j = t$—so the transform is its own inverse. By linearity over $\mathbb{F}_2$, on **any** incoming stream the outgoing bit at sweep $t$ is the incoming bit XOR $m_{t \bmod L}$. Crucially, this holds even when earlier counters modify the incoming stream dynamically.

---

## Building a starting queue

Each **command** takes two sweeps, specifying a first-sweep sign bit ($0$ = increment, $1$ = decrement) and a second-sweep lane bit for each counter. Given a nonempty even number of commands, let $L$ be the smallest power of two at least twice that count, and pad to $L/2$ commands with cancelling pairs of all-increment / all-decrement commands (zero second-sweep bits) starting at a logical instruction boundary.

For $r$ counters, let $d_j$ be the length-$L$ stream of desired lane bits at counter $j$ (interleaving both sweeps of each command), with $d_0 = d_{r+1} = 0$. Writing $W = \texttt{aaaeaeae}$, the starting queue for initial values $v_1, \ldots, v_r \ge 0$ is:

$$
C(d_0 \oplus d_1)\; W^{2^{4+4v_1}}\; C(d_1 \oplus d_2)\; W^{2^{4+4v_2}}\; \cdots\; C(d_{r-1} \oplus d_r)\; W^{2^{4+4v_r}}\; C(d_r)
$$

started at cut bit $0$ (pointwise XOR). Because the clock masks telescope, counter $j$ sees $d_j$ XOR the starting cut XOR the width parities of earlier data blocks, and the outgoing cut is the starting cut XOR the parities of **all** data blocks—providing the feedback channel for the zero test.

---

## Counters and guarded instructions

### Exponential counters and underflow feedback

At the start of a command, a counter holding exponent $E \ge 0$ is the word $W^{2^E}$. Tracing the two lanes of a single tile $W = \texttt{aaaeaeae}$:

- **Lane 0 (increment):** reads `a, a, a, a` $\to$ `bbbb`.
- **Lane 1 (decrement):** reads `a, e, e, e` $\to$ `b`.

On the second sweep, any **even** run of `b` letters regenerates one copy of $W$ per pair on either lane (both lane 0 and lane 1 read half the `b`s). Therefore:
- Lane 0 turns $W^{2^E}$ into $b^{4 \cdot 2^E}$ and then $W^{2^{E+1}}$, incrementing $E$ by $1$.
- Lane 1 with $E \ge 1$ turns $W^{2^E}$ into $b^{2^E}$ (still even) and then $W^{2^{E-1}}$, decrementing $E$ by $1$.
- **Underflow ($E = 0$, lane 1):** $W^1$ turns into a single `b`. On the second sweep, reading that `b` (on lane 0) regenerates $W^1$—leaving $E = 0$—and because `|b| = 1` is odd, it **toggles the cut bit** for the next command.

Notice two clean invariants: every first-sweep data block has even width ($8 \cdot 2^E$), and on the second sweep only this singleton `b` can alter a downstream lane—while all other (even) runs produce the same output regardless of lane.

### A 12-command zero-guard instruction

At the start of a logical instruction, the cut is $0$ and each logical counter value $v \ge 0$ is stored with exponent $E = 4 + 4v$ (a bias of 4, scaled by 4).

To update every passive counter by a chosen logical delta $a \in \{-1, 0, +1\}$ **if and only if** a designated tested counter is zero, emit the following 12 commands. The columns show the programmed first-sweep signs (`+` = lane 0, `-` = lane 1); each passive counter uses the column matching its target delta $a$:

| Commands | Tested | Passive ($a=+1$) | Passive ($a=0$) | Passive ($a=-1$) |
|---|---|---|---|---|
| 1–4 (remove bias) | `----` | `+-+-` | `+-+-` | `+-+-` |
| 5–6 (first probe) | `-+` | `+-` | `+-` | `-+` |
| 7–8 (second probe) | `-+` | `+-` | `-+` | `-+` |
| 9–12 (restore bias) | `++++` | `+-+-` | `+-+-` | `+-+-` |

All second-sweep lane bits are `0`, **except** at the tested counter in commands 6 and 8, where the bit is `1`.

Let's trace both branches after commands 1–4 remove the bias of 4 from the tested counter (leaving exponent $4v$):

- **Nonzero branch ($v > 0$):** The tested counter has exponent $4v \ge 4$, so no underflow occurs. Every probe executes its programmed signs, and each pair cancels on every counter. Commands 9–12 restore the bias, leaving all counters unchanged.
- **Zero branch ($v = 0$):** In each probe (5–6 and 7–8), the first `-` hits $E = 0$ and emits a singleton `b`. Both the cut and the tested counter's second-sweep bit are `0`, so the singleton is read, regenerates $W$, and flips the cut to `1` for the next command. That flipped cut reverses **every** programmed sign in the second command of the probe:
  - the tested counter's `+` becomes `-`, decrementing at $E = 0$ again; its second-sweep bit is `1`, canceling the cut `1` so the singleton is read on lane 0 again, regenerating $W$ and flipping the cut back to `0`;
  - every passive counter executes the opposite of its second programmed sign—which equals its **first** programmed sign, applying it twice.

Summing the two probes on the zero branch changes each passive exponent by $+2 + 2 = +4$ (for $a=+1$), $+2 - 2 = 0$ (for $a=0$), or $-2 - 2 = -4$ (for $a=-1$), i.e., $4a$ exponent units—one logical step.

Because every passive counter enters with exponent at least $4$, it can absorb the intermediate probe steps without ever hitting $E = 0$, even on a false guard. A requested logical decrement ($a = -1$) on a true guard requires a positive logical operand ($v \ge 1$, exponent $\ge 8$), so every counter again exits with exponent at least $4$. This preserves the invariant across any sequence of valid guarded updates.

---

## Examples

### Doubling a block by hand

Start with a single copy of $W = \texttt{aaaeaeae}$. Each arrow below is one literal 2-tag step:

```text
aaaeaeae → aeaeaeb → aeaebb → aebbb → bbbb
bbbb → bbaaaeaeae → aaaeaeaeaaaeaeae
```

The first sweep reads four `a`s (producing `bbbb`); the second reads two `b`s and leaves two copies of $W$. Starting with any positive number of copies doubles them in two sweeps, since both $W$ and `bbbb` have even length.

### Counting periods with a zero guard

Consider the instruction *"if $X = 0$, increment $Y$."* The Python snippet below compiles this instruction and verifies two full periods against literal 2-tag execution on both branches:

```python
from parity_program import compile_program, guarded, verify

rows = guarded(0, [0, 1])  # Test X. On zero, leave X alone and add 1 to Y.
word, commands = compile_program(rows, [0, 0])
assert (len(word), len(commands)) == (1046, 16)
verify(rows, [0, 0], lambda n: [0, n], 2)
verify(rows, [1, 0], lambda n: [1, 0], 2)
```

One period takes 32 sweeps. Starting at `(0, 0)`, the first two checkpoints are `(0, 1)` and `(0, 2)`—you can see the first increment directly in the queue as the $Y$ block grows from 16 copies of $W$ to 256. Starting at `(1, 0)` keeps $Y$ at 16 copies at both checkpoints.

### FizzBuzz

Run `python3 -B six_symbol_fizzbuzz.py` to print the first 100 outputs of FizzBuzz directly from a single starting queue (which can run indefinitely). The first 16 outputs cross the first clock reset:

```text
1 2 Fizz 4 Buzz Fizz 7 8 Fizz Buzz 11 Fizz 13 14 FizzBuzz 16
```

The literal starting queue (reproduced in full in the [appendix](#appendix-fizzbuzz-input)) is 2,128 letters long, with its first letter at the head of the queue. Run `python3 -B six_symbol_fizzbuzz.py --initial` to print it, or `--steps 3` to inspect the first four full queues starting at step 0 (step 1 reads `D`, deletes `DD`, and appends `DDez`).

**How the queue works.** The queue consists of three clocks, a data block initially equal to one $W$, and a fourth clock. Each clock period has 16 slots of 4 sweeps (64 sweeps total):
- **Slots 1–15** emit one output token each. On sweep 0 of each slot, the alignment after clock 1 signals `Fizz` (at slots 3, 6, 9, 12, 15), and the alignment after clock 2 signals `Buzz` (at slots 5, 10, 15). Because 15 is a multiple of both 3 and 5, the same masks repeat on every lap.
- **Counting:** in each emitting slot, the data block doubles twice, so after output $n$ it holds exactly $4^n$ copies of $W$. When neither flag is set, the number is decoded as $\log_4(\text{copies of } W)$.
- **Slot 16** doubles once and halves once, emits nothing, and leaves the count ready for the next lap. Clock 4 restores alignment 0.

The runner applies the six productions literally to the clock words while storing the repeated data tile and its multiplicity symbolically (avoiding expanding $4^{100}$ tiles at output 100). See [six_symbol_fizzbuzz.py](six_symbol_fizzbuzz.py), and the [appendix](#appendix-fizzbuzz-input) for the bitmask reconstruction and literal 2,128-letter word.

### Increment once and halt

Give a source machine a single edge from entry `s` to halt `h` that increments $X$. The compiler automatically adds the return trip:

```python
from parity_program import bouncing_machine, compile_program

rows, values = bouncing_machine(["s", "h"], "s", "h", [0],
                                [("s", "+", 0, "h")])
word, commands = compile_program(rows, values)
```

| Completed periods | Direction | Source state | $X$ |
|---:|---|---|---:|
| 0 | Forward | `s` | 0 |
| 1 | Forward | `h` | 1 |
| 2 | Backward | `h` | 1 |
| 3 | Backward | `s` | 0 |
| 4 | Forward | `s` | 0 |
| 5 | Forward | `h` | 1 |

The source machine halts after one period, while the tag queue continues running. At checkpoints 1 and 5—2,048 sweeps apart (four periods of 512 sweeps)—the entire queues match identically, including every clock cell. Run `python3 -B parity_program.py` to reproduce both this whole-queue comparison and the guarded-counter checks.

---

## From counter machines to exact cycles

The universality reduction proceeds in two stages: a **front end** turns an ordinary deterministic counter machine into a reversible one, and a **compiler** turns the reversible machine into a tag queue.

### Source machines

A counter machine has nonnegative integer registers and finitely many edges. Each edge either tests a register for zero or positive, increments a register, decrements a positive register, or does nothing (no-op). We require the source machine to be:
- **deterministic** (at most one edge enabled at any configuration),
- **normalized** (its entry state has no incoming edges; its halt state has no outgoing edges), and
- **total on nonhalting states** (every nonhalting configuration, reachable or not, has an enabled edge).

Standard Minsky counter machines ("increment and go to", "decrement, or jump if zero") satisfy these conditions once a fresh entry state is added. Note that these are syntactic conditions on the machine, not on a particular run.

### Making the source reversible

To make an arbitrary source machine reversible, add a **history register** $H$ and a **work register** $K$, both initialized to $0$. Number the $N$ source edges $0, \ldots, N-1$. Conceptually, $H$ acts as a base-$(N+1)$ stack recording the sequence of edges taken so far.

Each source edge $e$ into state $q$ is replaced by a three-step gadget:
1. Apply the operation of $e$ and move to a private state unique to $e$; test $K = 0$ there.
2. Transfer $H$ into $K$ one unit at a time.
3. Enter a shared loop belonging to $q$ at offset $\mathrm{idx}(e)$. From offset $k$, the loop adds $N + 1 - k$ to $H$ and reaches the loop head; each pass through the head moves one unit from $K$ and adds $N + 1$ to $H$. When $K = 0$, the loop exits to $q$.

The net effect on the history register is:
$$
H \;\longmapsto\; (N+1)H + (N + 1 - \mathrm{idx}(e)).
$$
The remainder modulo $N + 1$ uniquely identifies which edge entered $q$, making every step invertible. Every gadget state has at most two incoming edges, distinguished by a zero test against a positive test or increment on the same register. The remaining one-sided tests ($K = 0$ in step 1 and $H > 0$ inside the loop) always succeed on runs starting from $H = K = 0$. The resulting machine halts if and only if the source does. (For an alternative front end using a doubling history counter, see [Morita, 1996](https://doi.org/10.1016/0304-3975(96)00081-3), Theorem 3.1.)

### Compiling a reversible machine (one step per period)

The compiler takes a deterministic counter machine with distinct entry and halt states (no incoming entry edge, no outgoing halt edge), an enabled edge at every reachable nonhalting configuration, disjoint enabled domains at each source state, and disjoint images at each destination state. The front end produces machines of exactly this form. From here on, "the source" refers to this reversible machine.

Alongside the data registers, the compiler allocates:
- a **state flag** for each state ($0$ = active, $1$ = inactive; only the entry flag starts at $0$),
- an **edge latch** for each edge (all initially $1$), and
- a **permanent zero register** (for unconditional updates).

Every update below uses the 12-command zero-guard instruction. One compiled period executes one source step in three phases:

1. **Select.** For each edge, temporarily add a mismatch bit to its source flag:
   - *positive test or decrement:* add $1$ if the operand is $0$;
   - *zero test:* add $1$ unconditionally, then subtract $1$ if the operand is $0$;
   - *increment or no-op:* mismatch is $0$.

   Decrement the edge's latch if the resulting source flag is $0$, then undo the mismatch updates in reverse order with opposite signs. Exactly the single enabled edge now has latch $0$.
2. **Apply.** For each edge, guarded by its latch being $0$, add $1$ to its source flag, subtract $1$ from its destination flag, and apply its data operation (combining updates to the same flag first, so self-loops leave flags unchanged). Exactly one edge fires, leaving the new state as the unique $0$ flag.
3. **Clear.** For each edge, run the selection test using its *destination* flag and the guard of its *inverse* operation, this time **incrementing** its latch. (Tests keep their predicates; the inverse of increment requires a positive result; the inverse of decrement is an unconditional increment; no-op is its own inverse.) Because edges into a destination have disjoint images, only the edge just taken passes—restoring all latches to $1$, all temporary flags, and the permanent zero.

All control registers are distinct from their update targets, and every enabled subtraction acts on a positive operand by the flag, latch, and source-machine invariants. The three scans are finite and fixed at compile time; concatenating their commands, dropping empty updates, and padding to a power-of-two period yields the compiled queue. Induction on periods confirms that the simulated configuration matches at every checkpoint.

### Turning halting into exact queue repetition

Create **forward** and **backward** copies of every source state. Keep the original edges in the forward copy, and reverse every edge (with its inverse operation) in the backward copy. Add two no-op turnarounds:
- from forward halt to backward halt, and
- from backward entry to forward entry.

Because entry has no incoming edge and halt has no outgoing edge, both turns are unambiguous in either direction. Start at forward entry.

- **If the source halts:** the bouncing machine traverses a finite path to halt and back, repeatedly. Checkpoint register values stay bounded. Within any period, each counter exponent can grow by at most the fixed number of commands, and each clock cell has width 4 or 5. Intermediate queues during a sweep consist of an old suffix plus part of the bounded next word, so physical queue length is globally bounded. Since the leading clock sustains every sweep and there are only finitely many words of bounded length over a finite alphabet, the deterministic run must eventually repeat a word identically.
- **If the source diverges:** its forward trajectory never repeats a configuration (by injectivity, any repetition would pull back to a predecessor of the fresh entry state, which does not exist). With finitely many control states, the registers must grow unboundedly across checkpoints, forcing unbounded physical queue lengths. An exact repetition at any tag step would trap the deterministic system in a periodic tail of bounded length—a contradiction.

This establishes both directions of the equivalence using only the six fixed productions. The reference Python implementation for the reversible stage is in [parity_program.py](parity_program.py).

---

## Formal verification in Lean

Two Lean 4 files carry the full mechanized proof: [SixSymbol.lean](SixSymbol.lean) compiles a reversible machine into the tag system, and [ReversibleCounter.lean](ReversibleCounter.lean) builds the reversible front end and composes both stages (importing `SixSymbol.lean` unchanged).

**End-to-end theorem (`ReversibleCounter.halt_iff_exact_cycle`).** For any source machine `m` with `std : Standard m` and input register file `input`:

```lean
(∃ n, (m.path input n).pc = m.halt) ↔
  ExactCycle (encode (rev m std.fresh) (liftInput input))
```

`ExactCycle w` requires two distinct tag-step counts reaching the same whole queue (stalling on a short queue does not count). `rev m` is the reversible front end, `liftInput` initializes $H = K = 0$, and `encode` computes the starting queue from the machine and input alone. The intermediate theorem `SixSymbol.halt_iff_exact_cycle` proves the same equivalence directly for `encode m input` under `Reversible m` and `m.live input`, both of which `ReversibleCounter.lean` discharges for `rev m`.

Each file ends with a concrete check: `SixSymbol.Example.input_positive_iff_cycle` proves `0 < x ↔ ExactCycle (encode Example.machine (fun _ => x))` for all natural numbers `x`, and `ReversibleCounter.Example.machine` proves a non-reversible `Standard` machine produces an exact cycle on input `3`.

**Rechecking locally** (Lean 4.19 via `lean-toolchain`; both main theorems use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`—see [Lean’s guide to checking proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)):

```sh
lean SixSymbol.lean
mkdir -p build
lean -o build/SixSymbol.olean SixSymbol.lean
LEAN_PATH=build lean ReversibleCounter.lean
```

The first five rows are in `SixSymbol.lean`, the last three in `ReversibleCounter.lean`:

| Theorem | What Lean checks |
|---|---|
| `seeded_clock`, `layout_sweep` | A seeded clock emits its periodic mask on either lane; each whole-layout sweep consists of literal tag steps, including odd-boundary crossings. |
| `gate_realized`, `compiled_periods` | Two-sweep commands realize the 12-command zero guard on a register bank, and the padded program executes successive periods on one queue. |
| `compiled_repeats_iff` | The queue repeats identically iff register files at period boundaries stay within a finite set (even if clock memories vary between visits). |
| `one_period`, `checkpoint_edge` | Select, Apply, and Clear realize the enabled forward or inverse transition; the turns at halt and entry realize the bouncing trajectory. |
| `halt_iff_exact_cycle` | Halting visits finitely many configurations in both directions; repetition on an infinite forward run contradicts reversibility and fresh entry. |
| `rev_reversible` | The front end has a fresh entry, terminal halt, and forward- and backward-deterministic edges. |
| `rev_live` | The run invariant ($K = 0$ between source steps, $H > 0$ inside the loop) ensures an enabled edge at every reachable nonhalting configuration. |
| `rev_of_halt`, `halt_of_rev` | Each source step finishes in a finite gadget run, and every front-end state tracks a source configuration, so both machines halt together. |

The sole external premise is Minsky's theorem (*Computation: Finite and Infinite Machines*, 1967) with routine normalization to a fresh entry and terminal halt (not formalized); Morita's reversible simulation is not needed.

---

## Is six minimal?

For deletion number 2, a single production table, finite starting queues, and exact queue repetition as the observable, what is the least alphabet size (counting erasers, with arbitrary finite appendants and computable encodings) that is universal? The construction above gives an upper bound of **six**.

### Lower bound for this clock architecture

If we reserve two letters for data and require a disjoint, closed clock alphabet (with an eraser) where each clock cell uses two fixed state words of opposite length parity that regenerate the prescribed state in one sweep on either lane, **four clock letters are necessary**—making $4 + 2 = 6$ optimal for this architecture.

**Proof sketch.** Suppose a three-letter clock alphabet $\{A, B, e\}$ implements both an integrator and a differentiator, and let $M$ be the $2 \times 2$ matrix counting $(A, B)$ in the appendants of $A$ and $B$. Summing the two lane outputs of either state word gives $M c_0 = M c_1 = c_0 + c_1$, so $M$ must be singular (otherwise $c_0 = c_1$ forces equal output lengths on both lanes, contradicting opposite state parities) with eigenvalue $2$. That leaves two cases:
- **Both off-diagonal entries positive:** $\mathrm{tr}(M) = 2$ and $\det(M) = 0$ force all entries to be $1$. Every state word parses into $n > 0$ appendant copies; unless each copy puts one live letter in each lane, both states end up with the same length parity. Otherwise every copy shares the same single difference transfer—either $1+X$ or $(1+X)^{-1}$—and positive powers of one cannot realize the other.
- **An off-diagonal entry zero:** diagonal entries are $2$ and $0$, so state words parse into $n > 0$ copies of the doubling letter's appendant $V$ plus erasers. Again, opposite-lane placement is forced, giving every copy the same transfer $(1 + bX)/(1 + aX) \in \{1,\, 1+X,\, (1+X)^{-1}\}$, whose positive powers still cannot supply both cells.

See [clock_obstruction.tex](clock_obstruction.tex) for the complete proof.

### Two five-symbol perspectives

- **Removing `D` (integrator-only horizon compiler):** Dropping `D` leaves an integrator-only clock that matches the six-symbol counters up to any chosen finite horizon $K$ (a power of two divisible by the period) by repeating each mask to length $K$ and seeding $K$ integrators, whose transfer $(1+X)^{-K} = 1/(1+X^K)$ copies inputs faithfully through sweep $K - 1$. In the zero-guard example from `(0, 0)` with $K = 32$, the $Y$ blocks match through sweep 32 before diverging at sweep 34 (512 vs. 128 copies of $W$).
- **Data-reloaded control:** The repository's other five-symbol table uses data itself to reload control—already demonstrating a second load from a retained payload, while recurring simulation from live output remains open (see [five-symbol-tag.md](five-symbol-tag.md)).

Proving six minimal in general would require ruling out data-reloaded control and every other five-symbol table and encoding.

---

## Appendix: FizzBuzz input

**Reconstructing the 2,128-letter word.** Number the 64 sweeps of a period as $t = 4(s-1) + u$ ($1 \le s \le 16$, $0 \le u < 4$) and define three 64-bit masks: $F_t = 1$ at offset 0 of slots 3, 6, 9, 12, 15; $B_t = 1$ at offset 0 of slots 5, 10, 15; $A_t = 1$ only at slot 16, offset 2; and 0 elsewhere. The initial queue is:
$$
C(F)\; C(F \oplus B)\; C(B \oplus A)\; W\; C(A).
$$
In hexadecimal (cell 0 = LSB), the four integrator seed vectors are `0101101101101101`, `0000110100101010`, `5454544554555444`, and `5555555555555555`. Prepending 64 copies of `DDez` to each and expanding its 64 cells gives lengths $522 + 518 + 536 + 8 + 544 = 2{,}128$. Because the data run stays even on every sweep (the single halving follows a doubling), clock 4 cancels $A_t$ and preserves cut bit 0 by induction.

```text
DDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIaaaeaeaeDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezII
```
