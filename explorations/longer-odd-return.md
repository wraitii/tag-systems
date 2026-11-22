# Longer odd returns with a fixed four-letter clock

Keep deletion two, clock productions I → ezII, D → DDez, z → e and e → ε, and data productions over a,b,z,e. The target is the first positive return from aⁿ to an all-a queue. A sweep reads alternate letters of the old word; an odd old length consumes the first output letter. The following argument concerns fixed sweep timings.

**Result.** If the even first return is at the second sweep boundary, no table can have its odd first return at a fixed fourth or later sweep boundary for every odd n ≥ 3. The result holds for appendants of arbitrary length. It also rules out a uniformly bounded delay with every odd first return postponed past sweep three. An input-dependent unbounded delay is possible.

## Keeping the crossing on the same lane

Write A for a, R for its appendant and T for the output of lane 1 of R. Lane 0 starts at index zero. Under the proposed later odd return, the two-sweep even return forces R to have even width, with lane 0 emitting just A. Indeed, an odd R would expose both lanes in an even number of R copies. All its letters would have to produce only a letters or nothing. That excludes a and z from R, and odd inputs would also be unary by sweep two. With even R the only possible producer of the single a is b, so b → a and the even positions of R contain one b and otherwise e. Consequently T consists of entire R packets and individual A or e letters.

Fix any proposed horizon H ≥ 4. Choose input n = 2M−1 with M a sufficiently large multiple of 2^(H+2). The first two nominal outputs are R^M and T^M, each missing its first letter physically. If T is empty, the computation cannot reach the target. Otherwise choose M large enough that a bounded number of crossings can be taken on each surviving branch.

At every later sweep up to H, an even number of identical nominal periods can be retained. For an even-width period, apply lane 1 to each copy. For an odd-width period, group copies in pairs and apply lane 1 to the pair. This uses at most one factor of two in the repeat count per sweep. The old physical length is odd, so the first letter of the new nominal output is consumed again. Thus the start lane is **always 1** on this family of inputs through the chosen horizon. A non-a letter in a repeating output cannot disappear by trimming just one letter. An empty output cannot yield the positive target.

## Why later synchronization fails

If T contains no R packets, it consists of A and e letters. Its output is a power of R or empty; a homogeneous R word on lane 1 regenerates T. Up to H the only possible positive unary return is the early one when T itself consists of a letters.

Otherwise T contains at least one R packet. Both R and T contain literal b. After processing T all words have a parsing over the tokens A,R,T: processing a packet R emits A or T, standalone A emits R when selected, and e disappears. Call a lane of T *clean* if it emits only a letters. Each packet contributes either A or T, so a clean lane is nonempty. On a clean lane every packet emits A and every standalone A is skipped. On the opposite lane every packet emits T and selected standalone A letters emit R. In particular the opposite lane emits a nonempty word entirely over R,T.

- **Neither lane of T is clean.** A preceding word containing T cannot have a unary output. If it contains only A and R, the even width of R means successive A tokens alternate lanes, so half of them emit R across the repeated word. If it is all R, its starting lane 1 emits T. These cases exclude a later unary output.
- **Lane 0 of T is clean.** The first T is entered on lane 1 and emits a word starting in R or T. Thereafter a first R emits T, and a first T again emits a word starting in R or T. This invariant applies to the nominal word, even after trimming its first physical letter. Repetition keeps a literal b in the physical queue at each boundary.
- **Lane 1 of T is clean and T is even.** Every T copy is read on that lane and the third boundary is already unary.
- **Lane 1 of T is clean and T is odd.** For a unary output every T must start on lane 1, and every A must be skipped, which also requires lane 1. But A and T are exactly the odd-width tokens. Successive odd-width tokens alternate entry lanes, and the repeated nominal word contains an even number of them. If there are none, the word consists of R tokens on lane 1 and emits T.

This exhausts all possibilities at sweep boundaries. It also controls first returns inside the later sweeps on these inputs: if both an old and new periodic word contain a non-a letter, the unconsumed old suffix retains one until a complete new period containing one has already been emitted. The repeat count can be made arbitrarily large for any fixed H.

## A six-letter example whose delay grows with the input

Set R = bbebezebez and b → a. Then lane 0 of R emits A and lane 1 emits T = aaeae. The odd-width T emits one R on lane 0 and two on lane 1. Given n = 2M−1 ≥ 3, write M = 2^d h with h odd. After one sweep the physical queue is R^M missing its first letter. Each time the current multiplicity m is even, the next two sweeps replace it by 3m/2 and keep the cut. At the first odd m = 3^d h, those sweeps replace it by (3m+1)/2 and clear the cut. One clean R sweep returns to unary. Thus the odd return has length (3^(d+1)h+1)/2 and takes 4+2d sweeps. Even n returns to a^(n/2) in two sweeps. The ends of R and T are z and e respectively, so an old nonunary suffix cannot disappear early while only a letters have been emitted in the final sweep.

This gives 3 → 5 in six sweeps, 5 → 5 in four, and 15 → 41 in ten. Only the first example gives the desired odd Collatz value.

## Pruning a search with the even timing freed

If a → R consists entirely of a letters, every tag step on unary queues changes the length by a constant. Otherwise each first step appends a non-a letter. To obtain unbounded unary first returns, b must emit a nonempty pure power a^j. Without such a producer every appendant that emits any a also emits a non-a letter. The final all-a suffix would then have bounded length.

There is also a length bound j ≤ 4. At the first return the last non-a letter in the stream of appended letters has just been deleted. It came from the latest copy of R containing a non-a letter, or from z → e. Let s be the length of the pure-a suffix of that appendant: it is either the fixed suffix length of R or zero. All subsequent nonempty appendants are a^j. The last deletion consumes either zero or one a after that final non-a letter. Therefore the return length is s or s−1 modulo j. The two possible suffix lengths cover at most four residues; even Collatz inputs require all positive return lengths. This bound uses literal first returns and does not assume any sweep timing.

The [standalone verifier](longer_odd_return.js) checks the variable-delay formula by literal deletions for n = 2 through 256. Its bounded searches test every input from 2 through 32, allowing both timings to vary. Each input gets eight sweeps and at most 512 letters at a sweep entry. The longer search enumerates all R of length at most ten containing b, with b → a^j for 1 ≤ j ≤ 4. These are finite screens, not impossibility proofs for longer rules or computations.
