# A universal six-symbol 2-tag system with cycle detection

The alphabet is `I D z e a b`. Read the first letter, delete the first two letters, and append the word assigned to the letter read. A queue shorter than two has no successor. The letter `e` has the empty appendant.

```text
I → ezII       D → DDez       z → e
a → b          b → aaaeaeae   e → ε
```

**Claim.** There is a computable encoding of a reversible counter machine and its input into a finite queue such that the machine reaches its halt state if and only if the tag queue eventually repeats exactly. The source machines satisfy the entry, halt, and determinism conditions stated below. The program and data are in the queue. The six productions are fixed.

### Program clock

A sweep reads alternate letters of the current word. A block entered at alignment $p$ passes $p$ on to the next block if its length is even and flips it if its length is odd. When a tag deletion crosses a sweep boundary, the next sweep starts at the second letter.

| Cell | State 0 | State 1 | Next state |
|---|---|---|---|
| Integrator | `ezII` | `eezII` | `p XOR s` |
| Differentiator | `DDez` | `DDeze` | `p` |

**One sweep of the physical queue.** Write a nominal word as a concatenation of blocks, with a cut bit $p$. The physical queue is the nominal word with its first $p$ letters removed. In a block $w$ entered on lane $u$, concatenate the productions at zero-based indices $u,u+2,\ldots$. Pass $u\oplus (|w|\bmod 2)$ to the next block. Concatenate the resulting blocks to obtain the next nominal word. The outgoing lane at the end of the old word is the next cut bit. Indeed, an even physical length ends on an ordinary two-letter deletion. An odd length leaves one old letter, whose deletion consumes the first appended letter too. In the constructed queues the leading clock already produces a whole cell on either lane, so this crossing is always possible. Each sweep takes exactly the ceiling of half the old physical length in tag steps.

**Clock identity and seed.** In either cell the outgoing bit is $y=p\oplus s$ by width parity. Reading positions 0,2,… and 1,3,… in each displayed word gives the next-state entries in the table. Thus a differentiator stores the preceding input, and an integrator stores its preceding output. With initial state zero their respective input-output maps on streams are multiplication by $1+X$ and division by $1+X$, where $X$ delays a bit stream by one sweep and all coefficients are modulo two. These formulas follow from $y_t=p_t+p_{t-1}$ and $y_t=p_t+y_{t-1}$ with zero past.

For a mask $m_0,\ldots,m_{L-1}$, with $L$ a power of two, define the literal clock word $C(m)$ as $L$ copies of `DDez` followed by $L$ integrators in order $i=0,\ldots,L-1$. Use `eezII` at $i$ if its seed bit is 1 and `ezII` otherwise. To compute seed bit $i$, XOR all $m_j$ for which the set bits of $i$ are a subset of those of $j$.

To prove the formula, first set all seeds to zero. The two banks cancel on every input stream. Now switch on seed $i$ alone. Its cell emits the constant stream of ones on zero input, and there are $L-1-i$ integrators after it. Its contribution is
$$
(1+X)^{-(L-i)}=(1+X)^i/(1+X^L).
$$
The denominator repeats the numerator every $L$ sweeps. Factoring the numerator into $1+X^{2^k}$ over the set bits $k$ of $i$ shows that it has a 1 at precisely the subsets of $i$. The output at $t<L$ therefore XORs the seeds over supersets of $t$. Applying this transform twice counts each superset $j$ once for every intermediate subset between $t$ and $j$. That count is odd exactly when $j=t$, proving that the transform is its own inverse. By linearity, on **any** incoming stream the outgoing bit at sweep $t$ is the incoming bit XOR $m_{t\bmod L}$. This includes inputs changed by the counters on earlier sweeps.

### From commands to a literal starting word

A command takes two sweeps. For each counter specify a sign bit on the first sweep (0 for increment, 1 for decrement) and a lane bit on the second. Start with a nonempty even number of commands. Let $L$ be the least power of two at least twice that number. Pad to $L/2$ commands with pairs of all-increment, all-decrement commands, both with zero second-sweep bits. Padding starts at a logical instruction boundary, so the pair cancels.

For $r$ counters let $d_j$ be the resulting length-$L$ stream of desired lane bits at counter $j$, interleaving the two sweeps of each command. Write $d_0=d_{r+1}=0$ for all-zero streams and $W=$ `aaaeaeae`. Given initial nonnegative values $v_j$, concatenate, for $j=1$ through $r$, the two words
$$
 C(d_{j-1}\oplus d_j)\quad W^{2^{4+4v_j}},
$$
then append $C(d_r)$ and start at cut zero. XOR acts pointwise. Since the clock masks telescope, the actual lane at counter $j$ equals $d_j$ XOR the starting cut XOR the width parities of earlier data blocks. The outgoing cut equals the starting cut XOR the parities of **all** data blocks. This gives the feedback used by the zero test.

### Counters and conditional instructions

At the start of a command a counter is $W^{2^E}$. Lane 0 of $W$ emits `bbbb` and lane 1 emits `b`. An even run of $b$ letters regenerates one $W$ per pair on either lane. Thus the two sweeps change $E$ by $+1$ or $-1$ according to the actual first lane. A decrement at $E=0$ produces a single $b$. Reading that $b$ regenerates one $W$ and leaves $E=0$. Its odd width toggles the cut for the next command. All first-sweep data blocks have even width. On the second sweep only this exceptional run can change a downstream lane, and the other even runs give identical outputs on both lanes.

**A complete zero-guard instruction.** At entry the cut is zero and each logical value $v$ has exponent $4+4v$. To change each passive counter by a specified logical amount $a$ in $\{-1,0,1\}$ if the tested counter is zero, use the following twelve commands. The columns show the programmed signs. Each passive counter gets its own column according to $a$.

| Commands | Tested | Passive $a=+1$ | Passive $a=0$ | Passive $a=-1$ |
|---|---|---|---|---|
| 1–4, remove bias | `----` | `+-+-` | `+-+-` | `+-+-` |
| 5–6, first probe | `-+` | `+-` | `+-` | `-+` |
| 7–8, second probe | `-+` | `+-` | `-+` | `-+` |
| 9–12, restore bias | `++++` | `+-+-` | `+-+-` | `+-+-` |

All second-sweep bits are zero except at the tested counter in commands 6 and 8, where the bit is one. After removing the bias the tested exponent is $4v$. If $v>0$, each probe executes its programmed signs and all changes within the pair cancel. If $v=0$, the first decrement in each probe produces a singleton. The cut and the tested second-sweep bit are both zero there, so the singleton is read. The next command starts with cut one and reverses **every** programmed sign. The tested counter decrements again at zero. This time its second-sweep bit is one, so the actual lane is again zero and it regenerates $W$. The second singleton restores cut zero. Earlier passive runs are even, so neither singleton can miss its read.

Each probe therefore applies its first passive sign twice on the zero branch. Summing the two pairs gives $4a$ exponent units. The bias steps cancel on passive counters and restore the tested counter. They start with at least four exponent units, sufficient for the four probe steps even on a false guard. A requested logical decrement on a true guard requires a positive operand, so the exit again has every exponent at least four. This proves the instruction invariant, including the absence of accidental passive underflow, for any sequence of valid guarded updates.

### Example programs

**Double a block.** Start with just one copy of `W = aaaeaeae`. This is small enough to run by hand. Each arrow below is one literal tag step.

```text
aaaeaeae → aeaeaeb → aeaebb → aebbb → bbbb
bbbb → bbaaaeaeae → aaaeaeaeaaaeaeae
```

The first sweep reads four `a`s. The second reads two `b`s and leaves exactly two copies of `W`. Starting with any positive number of copies gives the same doubling in two sweeps, since each tile has even width and its four output letters also have even width.

**Count periods with a zero guard.** The source instruction is “if X is zero, increment Y.” The following Python builds the initial queue and checks two periods against the literal productions on both branches.

```python
from parity_program import compile_program, guarded, verify

rows = guarded(0, [0, 1])  # Test X. On zero, leave X alone and add 1 to Y.
word, commands = compile_program(rows, [0, 0])
assert (len(word), len(commands)) == (1046, 16)
verify(rows, [0, 0], lambda n: [0, n], 2)
verify(rows, [1, 0], lambda n: [1, 0], 2)
```

One period takes 32 sweeps. Starting at `(0,0)`, the first two checkpoints are `(0,1)` and `(0,2)`. You can see the first increment in the queue itself. Its Y block goes from 16 copies of `W` to 256. Starting at `(1,0)` keeps Y at 16 copies on both checkpoints.

**FizzBuzz.** Run `python3 -B six_symbol_fizzbuzz.py` to print the first 100 outputs. The same starting queue can continue indefinitely. Its first 16 outputs cross the first clock reset.

```text
1 2 Fizz 4 Buzz Fizz 7 8 Fizz Buzz 11 Fizz 13 14 FizzBuzz 16
```

The literal initial input (see end) is one line of 2,128 tag letters. Its first letter is the head of the queue. Run `python3 -B six_symbol_fizzbuzz.py --initial` to print the same word. Use `--steps 3` to print four full queues, starting at step zero. The first step reads `D`, deletes the leading `DD`, and appends `DDez`.

The queue contains three clocks, a data block initially equal to one `W`, and a fourth clock. Each clock period has sixteen slots of four sweeps. Slots 1 through 15 emit a token. On the first sweep of each slot, the alignment after clock one signals Fizz at slots 3, 6, 9, 12, 15. The alignment after clock two signals Buzz at slots 5, 10, 15. Both bits can be set. Since 15 is a multiple of both divisors, the same masks work on every lap.

**Reconstructing the 2,128-letter input.** Number the sweeps $t=4(s-1)+u$ with slot $1\le s\le16$ and offset $0\le u<4$. Define three 64-bit masks. Set $F_t=1$ at offset 0 of the five Fizz slots above, $B_t=1$ at offset 0 of the three Buzz slots, and $A_t=1$ only at slot 16, offset 2. All other bits are zero. The literal initial word, in concatenation notation, is
$$
 C(F)\ C(F\oplus B)\ C(B\oplus A)\ W\ C(A).
$$
For a direct expansion, the four integrator seed vectors in that order are `0101101101101101`, `0000110100101010`, `5454544554555444`, and `5555555555555555` in hexadecimal, with cell 0 given by the least significant bit. Before each vector put 64 copies of `DDez`, then expand its 64 cells by the clock rule above. The word lengths are $522+518+536+8+544=2128$. At offset 0 the first two outgoing lanes give $F_t,B_t$, and the data lane on every sweep is $A_t$. The last clock cancels it because the data run is even on all these sweeps (a sparse read occurs only after a doubling). Hence the next cut stays zero. This establishes the alignment assumption for every slot by induction.

The number itself lives in the queue. In each emitting slot the data block doubles twice, so after output number `n` it contains exactly `4**n` copies of `W`. If both flags are clear, decode that count by taking its base-four logarithm. Slot 16 doubles once and halves once, emits nothing, and leaves the count ready for the next lap. The fourth clock restores the starting alignment. The runner applies the six productions to the clock words and stores the repeated data tile and its exact multiplicity separately. At output 100 that saves expanding `4**100` tiles. [Runnable FizzBuzz program](six_symbol_fizzbuzz.py)

**Increment once and halt.** Give the source machine one edge, from entry `s` to halt `h`, which increments X. The compiler adds the return trip.

```python
from parity_program import bouncing_machine, compile_program

rows, values = bouncing_machine(["s", "h"], "s", "h", [0],
                                [("s", "+", 0, "h")])
word, commands = compile_program(rows, values)
```

| Completed periods | Direction | Source state | X |
|---:|---|---|---:|
| 0 | Forward | s | 0 |
| 1 | Forward | h | 1 |
| 2 | Backward | h | 1 |
| 3 | Backward | s | 0 |
| 4 | Forward | s | 0 |
| 5 | Forward | h | 1 |

The source reaches halt after one period. The tag queue keeps running. At checkpoints 1 and 5 the entire words match, including every clock cell. Those checkpoints are 2,048 sweeps apart (four periods of 512 sweeps). Run `python3 -B parity_program.py` to reproduce the whole-queue comparison and the guarded-counter checks.

### From counter machines to exact cycles

Take a deterministic reversible counter machine with nonnegative registers, distinct entry and halt states, no incoming entry edge, no outgoing halt edge, and one enabled edge at each reachable live configuration. Each edge tests zero or positive, increments, decrements a positive register, or leaves the registers alone. Distinct edges have disjoint enabled domains at a common source and disjoint images at a common destination. The external universality theorem used here is Morita's reversible simulation of deterministic counter machines (Theorem 3.1). Its construction starts with a fresh entry. An ordinary universal counter program can be given a fresh entry and a single terminal halt before this simulation. [Morita, 1996](https://doi.org/10.1016/0304-3975(96)00081-3)

**One source step per period.** In addition to the data registers, allocate a flag for each state (0 active, 1 inactive), a latch for each edge (initially 1), and a permanent zero register for unconditional updates. Initialize only the entry flag to 0 among the state flags. Use the twelve-command instruction above for every update below.

1. **Select.** For each edge, temporarily add a mismatch bit to its source flag. For a positive test or decrement, add 1 if its operand is zero. For a zero test, add 1 unconditionally then subtract 1 if the operand is zero. Increment and no-op have mismatch zero. Decrement the edge latch if the resulting flag is zero, then undo the mismatch operations in reverse order with opposite signs. Exactly the enabled edge now has latch 0.
2. **Apply.** For each edge, guarded by its latch being zero, add 1 to its source flag, subtract 1 from its destination flag, and apply its data change. Combine updates to the same flag before emission, so a self-loop changes no flag. Exactly one edge fires and the new state has the unique zero flag.
3. **Clear.** For each edge use its destination flag and the guard of its inverse to select as in step 1, this time **incrementing** its latch. Tests retain their predicates, the inverse of increment requires a positive result, and the inverse of decrement is an unconditional increment. No-op is its own inverse. Disjoint images ensure that exactly the edge just taken passes. All latches are again 1, all temporary flags are restored, and the permanent zero remains zero.

All controls are distinct from their update targets. Every enabled subtraction has a positive operand by the flag, latch, or source-machine invariant. The scans are finite and fixed at compile time. Concatenate their commands, omit empty updates, and pad as above. Induction on periods now gives the simulated configuration at every checkpoint.

**Halt as exact queue repetition.** Make forward and backward copies of every source state. Keep the original edges in the forward copy and reverse each edge with its inverse operation in the backward copy. Add a no-op from forward halt to backward halt and another from backward entry to forward entry. The missing edges at entry and halt make both turns unambiguous in either direction. Start at forward entry.

If the source halts, this machine runs along a finite path and back, repeatedly. Checkpoint counters are bounded. Within a period each exponent can increase by at most the fixed number of commands, and each clock cell has width four or five. Intermediate tag queues are bounded too, since during a sweep they consist of an old suffix and part of the bounded next word. The leading clock sustains every sweep. Finitely many bounded words on a finite alphabet force exact repetition.

If the source runs forever, its forward trajectory has no repeated configuration. Injectivity would pull a repetition back to a predecessor of the fresh entry. Finite control then forces unbounded counters at checkpoints, hence unbounded physical queue lengths. Any exact repetition at any tag step would give a periodic deterministic tail with bounded lengths, a contradiction. This proves both directions using only the six fixed productions. The reference implementation is [parity_program.py](parity_program.py).

### Checking the equivalence in Lean

**The machine-checked theorem is `SixSymbol.halt_iff_exact_cycle`.** For a finite reversible machine `m` and an input register file, Lean proves this statement about the computed starting word.

```lean
(∃ n, (m.path input n).pc = m.halt) ↔ ExactCycle (encode m input)
```

Read `∃ n` as “at some source step” and `↔` as “if and only if.” On the right, `ExactCycle w` requires two different tag-step counts at which the run from `w` successfully reaches the same whole word. Reaching a short queue twice by treating it as stationary would fail this definition. The hypotheses `Reversible m` and `m.live input` concern the source machine: its enabled edges are forward- and backward-deterministic, entry has no incoming edge, halt has no outgoing edge, and each reachable nonhalting configuration can step. The encoder computes its word from the machine and input alone. [Lean definitions and proofs](SixSymbol.lean)

For a small example, read `Example.input_positive_iff_cycle` at the end of the file. Its three source edges send a positive input straight to halt and a zero input into a loop that increments forever. Lean proves `0 < x ↔ ExactCycle (encode Example.machine (fun _ => x))` for **every** natural number `x`.

To recheck the file with Lean 4.19 and its standard library, run this command from the project directory. Elan uses the adjacent `lean-toolchain` file to select the version.

```sh
lean SixSymbol.lean
```

The line for `halt_iff_exact_cycle` reports the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. A proof placeholder would add `sorryAx` to this list. [Lean’s guide to checking proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

| Theorem | What Lean checks |
|---|---|
| `seeded_clock`, `layout_sweep` | A seeded clock emits the selected periodic mask on either lane. Each whole-layout sweep consists of literal tag deletions, including the crossing at an odd boundary. |
| `gate_realized`, `compiled_periods` | The two-sweep commands execute the twelve-command guard on a register bank. The padded program executes successive periods on one queue. |
| `compiled_repeats_iff` | The queue repeats exactly when the register files at period boundaries range over a finite set. Clock memories can vary between visits. |
| `one_period`, `checkpoint_edge` | Selection, update, and latch clearing implement the enabled forward or inverse transition. The turns at halt and entry realize the bouncing trajectory. |
| `halt_iff_exact_cycle` | A halting run visits finitely many source configurations in both directions. Repetition on an infinite forward run would contradict reversibility and fresh entry. |

The formal reduction covers the tag system and the encoder defined in Lean. Morita’s universality theorem for reversible counter machines supplies the external premise for the universality conclusion. The Python implementation is an executable reference. [Morita, 1996](https://doi.org/10.1016/0304-3975(96)00081-3)

### Is six minimal?

Fix deletion number two, one production table, finite starting queues, and exact queue repetition as the observable. Ask for the least alphabet size for which a total computable encoder maps each machine and input to a queue that eventually repeats exactly when the machine halts. Count every letter in the table, including an eraser. Allow arbitrary finite appendants and queue encodings. Under this definition the construction gives an upper bound of six.

There is a lower bound *for this clock design*. Reserve two letters for data and require a disjoint, closed clock alphabet containing an eraser. Require each clock cell to use two fixed state words of opposite length parity and to regenerate the prescribed state word in one sweep on either alignment. The three-letter clock obstruction shows that no such three-letter alphabet can implement both the integrator and differentiator with one table. These requirements therefore cost at least four clock letters plus two data letters, and the displayed table attains six. [Clock obstruction proof](clock_obstruction.tex)

**Proof of the clock restriction.** Write $A,B$ for the two letters besides the eraser. Let $M$ be the two-by-two matrix whose column for a letter counts the occurrences of $A,B$ in its appendant. Let $c_0,c_1$ count them in the even and odd state words of either proposed cell. From either word the two lanes output the two state words once each. Adding their counts gives $Mc_0=Mc_1=c_0+c_1$. If $M$ were invertible we would have $c_0=c_1$. The two lanes of a given word would then also select identical count vectors, since their images under $M$ agree. Their outputs would have equal lengths, contradicting the opposite state parities. Thus $M$ is singular and its nonzero vector $c_0+c_1$ has eigenvalue two. A cell consisting entirely of erasers could never regenerate its odd word.

*If both off-diagonal entries are positive*, trace two and determinant zero force all four entries to be one. Each of the two appendants contains one $A$ and one $B$. Each state word, being an output, consists of copies of those appendants. Each copy contributes one of each letter, and the count equation gives the same number $n>0$ of copies in both states. Use the parsing induced by production on each sweep.

- If both types of copy place their two live letters in a single lane, selecting a copy emits one appendant of each type. The output has $n$ copies and hence fixed length.
- If exactly one type places both in a single lane, exactly half of its copies must be selected to preserve the total of $n$. Its multiplicity is even in either state. The other multiplicity has parity $n\bmod 2$, so both states have the same width parity.
- Otherwise each copy has one live letter per lane, and each regenerates exactly one copy. The two types must have opposite widths modulo two for the state parities to differ. Label a copy by its width bit $s$. With incoming bit $u$ it passes $u+s$ and produces type $u+f(s)$ for a fixed Boolean function $f$. Compare two input histories from the same initial word. If $f$ is constant, each copy has difference transfer $1+X$ by the differentiator recurrence. If $f(s)=s+c$, each has transfer $(1+X)^{-1}$ by the integrator recurrence. All copies use the same rule. A row of $n$ has the corresponding $n$th power. No positive powers of just one of these transfers can realize both required transfers, even allowing the two cells different lengths.

*If an off-diagonal entry is zero*, the diagonal entries are two and zero. Call the letter with diagonal two $G$, its appendant $V$, and the remaining letter $H$. If $V$ lacks $H$, neither appendant produces $H$, so $H$ is absent from both state words. Otherwise triangularity forces $H$ to emit only erasers. In either case every state word has a production parsing into $n$ copies of $V$ with intervening or exterior erasers. Each copy contains two $G$s. Counting $G$s across both lanes gives the same $n>0$ in both states.

If both $G$s occupy the same lane within $V$, half the copies must see each alignment to produce $n$ new copies. Thus the total number of selected auxiliary letters inside copies is fixed as well. Exterior erasers emit nothing. Both outputs have the same length.

If the $G$s occupy opposite lanes, each copy reproduces once, with a prefix and suffix of erasers emitted by the selected auxiliary letters in that copy. Keep these erasers attached to their producing copy. Let $f,g$ give the parities of the new prefix and suffix as functions of the alignment at $V$, with Boolean slopes $a,b$ respectively. For two histories starting from the same word, call the differences at the start of this block, at its core $V$, and at its end $u,p,v$. The previous sweep determined today's padding, while the core has fixed width. Hence $p=u+aXp$ and $v=p+bXp$. Each copy has difference transfer $(1+bX)/(1+aX)$, equal to $1$, $1+X$, or its inverse. All copies again use the same transfer. Its positive powers cannot supply both desired cells. This exhausts the possible matrices and proves the restricted lower bound.

For five symbols there are two instructive cases. Removing `D` gives an integrator-only compiler that can match the counter blocks for any chosen finite horizon by enlarging the initial clock. Indeed, for a power of two $K$ at least the horizon and divisible by the original period, repeat each mask to length $K$ and seed just $K$ integrators. Their zero-state transfer is $(1+X)^{-K}=1/(1+X^K)$, which copies every input stream exactly through sweep index $K-1$. The same seed proof supplies the repeated mask. Induction along blocks and sweeps gives the same data evolution throughout that prefix. For the zero-guard example from `(0,0)` with a 32-sweep horizon, the Y blocks agree through sweep 32. At sweep 34 the six-symbol queue has 512 copies of `W` in Y and the five-symbol queue has 128. Choosing a horizon in advance leaves open how one finite queue could handle an arbitrarily long computation.

The project's other five-symbol table uses data to reload control. It already performs a second load from a retained payload, and a recurring simulation from live output remains open. Proving six minimal for the cycle observable would require ruling out that approach and every other five-symbol table and encoding. The clock obstruction alone leaves that question open. [Five-symbol writer and readback](five-symbol-tag.md)

---

### Fizzbuzz input 

DDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIezIIDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIezIIezIIeezIIezIIeezIIezIIeezIIezIIaaaeaeaeDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezDDezeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezIIeezIIezII
