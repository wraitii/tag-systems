# Seven symbols for unary Collatz and universality at deletion two

Read the first letter, delete two letters, and append its production. A queue shorter than two halts. The fixed table is

```text
I → ezII       D → DDez       z → e       e → ε
a → bc         b → a          c → ababeb
```

The three data letters serve both computations. Starting from `aⁿ` gives the shortcut Collatz orbit up to 1. Starting with clock and register blocks gives the same reversible-counter-machine and exact-queue-repetition reduction as the six-symbol construction. The new ingredient required for the latter claim is a guarded update that works with the new data rules. The finite lane schedules below specify that update.

## Unary first return

Write R = `bc` and T = `ababeb`. Each a emits R. If n = 2k, one sweep gives Rᵏ and the next reads its b letters, leaving aᵏ.

For n = 2k+1 ≥ 3, the first sweep leaves Rᵏ⁺¹ with the first b consumed. The second reads k+1 copies of c and leaves Tᵏ⁺¹ with the first a consumed. The third reads three b letters per tile and its final deletion crosses into the emitted a letters. The result is a³ᵏ⁺². All crossings have an available partner for k ≥ 1. Until the final deletion of the return sweep, at least one non-a letter remains. Thus the first positive unary return gives n/2 or (3n+1)/2, and a¹ halts.

## Register arithmetic

A programmed lane is 0 for even positions of a nominal block or 1 for odd positions, starting at index zero. The four clock rules, their seed formula, the physical sweep convention, and the XOR of adjacent desired masks are exactly those of [the clock construction](six-symbol-tag.md). In particular, the actual lane equals the programmed bit XOR the entry cut XOR the width parities of earlier data blocks. An odd data width flips that bit for later blocks and flips the next sweep's entry cut when it is the only odd width. A leading clock supplies the partner needed for a physical boundary crossing, including when a data block has just one letter.

| Nominal block | Output on lane 0 | Output on lane 1 |
|---|---|---|
| Rᵐ | aᵐ | Tᵐ |
| aᵐ | R^ceil(m/2) | R^floor(m/2) |
| Tᵐ | R²ᵐ | a³ᵐ |

Only aᵐ can have odd width. In particular, the same tile T that supplies the three a letters for Collatz supplies two copies of R on its other lane. Starting from Rᵐ with m even and cut zero, lane string `00` halves m and `10` doubles it. The four-sweep string `0010` restores it.

Encode register v ≥ 0 by R raised to the power 2^(8+4v). A guarded instruction tests one register and, when it is zero, adds any prescribed delta in {-1,0,+1} to each passive register. A subtraction on the true branch requires a positive operand.

## The 64-sweep guard

1. **Expose the test in 16 sweeps.** Give the tested register `00` eight times. Every passive register runs `0010` four times. The test multiplicity is now 2^(4v). The cut stays zero throughout.
2. **Run two 16-sweep probes.** The tested register uses `0000101000100010` for each. Choose each passive register's mask independently from the table below. For delta +1 use the +2 row twice. For zero use +2 then −2. For −1 use −2 twice. The signed numbers in the table are changes of the exponent on the true branch.
3. **Restore the bias in 16 sweeps.** Give the tested register `10` eight times. Passives run `0010` four times. Each register is back in checkpoint form, and the cut is zero.

| Passive position | Exponent change if tested zero | Programmed lanes for one probe |
|---|---:|---|
| Before test | +2 | `1010101001010101` |
| Before test | −2 | `1010100101100101` |
| After test | +2 | `0110101010010100` |
| After test | −2 | `0110100110100100` |

**Finite verification of the probe.** On a positive test, start at R with relative exponent zero and apply the three lane identities above. The tested path never takes the T-to-a branch, returns to R with exponent change zero, and reaches minimum relative exponent −2. Its starting exponent is at least 4. All widths are even and every passive mask returns to R with exponent change zero.

On a zero test start with the single tile R. Applying the same identities with the physical cut gives these nominal states after each sweep:

```text
a, R, T, a³, R², a², R, a, R, T, R², T², a⁶, R³, a³, R
```

The cumulative parity bits seen by passives before the test are `0011100001111111`. Those seen after it are `0111000011111110`. The latter includes the current tested width. The outgoing cut after the last sweep is zero. XOR the appropriate history with a passive mask and apply the lane table. Its net exponent change is exactly the signed value in the table, and all its T steps use lane zero.

Eight units of exponent bias suffice. Each passive path starts and ends in R and has at most eight halvings per probe. On a true subtraction the initial exponent is at least 12, leaving at least 10 for the second probe. The zero delta takes its +2 probe first. On false branches both probes have net zero. Thus every passive a run consumed by a halving is even, validating the parity histories. The program checks these finite identities directly in `check_probe()`.

## Universality and the observable

Each guarded instruction occupies 64 sweeps. Concatenate instructions and pad to a power of two with four-sweep identities. The seeded clock banks then supply the masks on every lap, including in the presence of data-dependent cuts. An instruction restores cut zero before the next instruction. This implements the guarded language used in [the existing select/apply/clear compiler](parity_program.py).

More explicitly, take the forward/backward counter machine from that compiler and replace each guarded operation by the 64-sweep implementation above. At every period boundary the registers encode the same source configuration as in the original proof. If the source halts, the simulated forward/backward path is bounded. The clocks have bounded cell widths, and within a period a bounded register has bounded intermediate words, so some entire physical queue repeats. If the source never halts, the reversible forward path from a fresh entry has unbounded registers. Thus physical checkpoint lengths are unbounded, which is impossible after an exact repetition in a deterministic tag system. This gives the same halt-if-and-only-if-exact-repetition reduction.

[The reference program](seven_symbol_collatz.py) provides the mask compiler and a checked translation from the existing bouncing-machine compiler. For example:

```python
from seven_symbol_collatz import bounce_guards, compile_guards

guards, registers = bounce_guards(["s", "h"], "s", "h", [0], [("s", "+", 0, "h")])
initial_queue, period_in_sweeps = compile_guards(guards, registers)
```

Run `python3 -B seven_symbol_collatz.py` for the symbolic probe verification, literal unary returns from 2 through 1000, physical guard and padding tests, and a bouncing-machine register trace. The proof gives an upper bound of seven. Six-symbol minimality and a Lean formalization of this variant remain open here.
