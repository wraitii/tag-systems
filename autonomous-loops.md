# Autonomous loops in fixed 2-deletion tag systems

One round below is two sweeps. The initial queue holds all the input. In particular, no new symbols are supplied externally while a loop runs.

## Counted addition in the existing five-symbol table

The five-symbol clock proof is in [Counted addition](five-symbol-tag.md#counted-addition).

## A four-symbol program with a persistent odd-length cell

| Letter | Appendant |
|---|---|
| I | IIe |
| e | ε |
| a | b |
| b | aaaeaeae |

Write C = `IIe` and W = `aaaeaeae`. Either read lane of C emits exactly C. Its odd length flips the incoming alignment at the next block. The two lanes of W emit four or one copies of `b`, respectively. This uses the erasing letter for both the clock cell and the counter unit.

With three cells, define the physical boundary Q(p;A,B,T) by forming

    W^A C W^B C W^T C

and dropping the first p letters, where p is zero or one. A, B and T are raw multiplicities, including zero. The boundary records the alignment exactly, including when a tag deletion straddles a sweep boundary.

In the first sweep the lanes of the successive runs are p, 1−p, p. An increment-lane run emits 4m copies of b and therefore doubles after sweep two. A decrement-lane run emits m copies of b. The second sweep starts with the opposite phase since the whole uncut word has odd width. Its first odd decrement-lane run rounds up, its second rounds down, and so on. Each such odd run flips the outgoing phase. These observations determine the whole next boundary.

### A data-dependent first return

Let D(b,M) = Q(1;1,2^b,M), with b and M nonnegative. The dispatch condition is phase one and multiplicity one at A.

| Tape at entry | First return | Two-sweep rounds |
|---|---|---:|
| M = 2m+1 | D(b+1,m) | 1 |
| M = 2m, including zero | D(b+2,m) | 2b+5 |

On the odd branch A and T both have odd width on sweep two. A rounds up to one and T rounds down to m. B doubles and the two phase flips cancel.

On the even branch only A flips the phase. The first round gives Q(0;1,2^(b+1),m). The next b+1 rounds drain the exponent at B to zero. Its zero event switches the direction and yields Q(1;2^(b+2),1,2^(b+2)m). After b+2 further rounds A has multiplicity one again and the boundary is D(b+2,m). The powers of two guarantee exact divisions of the tape until the return. Before then either the phase is zero or A has multiplicity greater than one.

Three consequences follow.

- Starting at D(b,0), a single finite queue dispatches forever. Both A and B repeatedly reach zero exponent and change the clock direction. At dispatch number j, starting from j=0, the exponent at B is b+2j. No unread digits are available or required. The dispatch intervals grow, and the physical queue lengths are unbounded.
- Starting at D(b,2^h(2k+1)), the same markers and rules execute h even branches and one odd branch. After exactly h(2b+2h+3)+1 rounds the dispatcher is at D(b+2h+1,k). Thus an independently chosen suffix k is available for the next branch. In this encoding the timer is the power of two multiplying the odd part of the tape.
- For any positive M of bit length L, after consuming all L digits the exponent at B is b+2L−popcount(M). The autonomous empty-tape shuttle then continues.

### An exact-cycle predicate for the same table

Use two cells, form W^M C C, and drop its first letter. On the sparse lane an even M halves without a phase change. With even total cell parity the first odd M rounds **down** and switches the phase to zero. Write the initial positive M as 2^h u, where u is odd. After h+1 rounds there are (u−1)/2 units left. If u=1 the entire queue is C C, which repeats after three tag steps. If u>1 the surviving run doubles every round forever, precluding any earlier or later exact repetition. The initial queue therefore repeats eventually exactly when M is a power of two.

The [four-symbol verifier](four_symbol_loop.py) checks literal individual tag steps, repeated-tile whole-word equality, first-return times, compositions and the cycle predicate. The two-cell predicate and the three-cell dispatcher are two initial layouts of the same fixed table. These results do not establish universal computation or an alphabet minimum.
