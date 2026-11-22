# What the delayed eraser buys at deletion two

Keep the four clock rules and take a → R = bbeaeaeaez, b → a. Write A for a and T for a R³ e. The two lanes of R emit A and T. The two lanes of T emit R T³ and AAA. Thus even unary inputs return in two sweeps and odd inputs in three. On an odd input of length 2k+1 the successive nominal outputs are R^(k+1), T^(k+1), and a^(3k+3), each with its first letter consumed by the boundary crossing. The last queue has length 3k+2.

## An obstruction for arbitrary appendants

Assume the same two- and three-sweep first returns for all inputs, with appendants for a,b over a,b,z,e, and the fixed z → e → ε chain. Let R denote the appendant of a. No fixed finite lane program on the register R^m can double its multiplicity for every sufficiently divisible m.

R must contain a letter other than a, since the first step leaves the unary a words. If R had odd width, even inputs producing an even number of R packets would read both lanes of R, forcing every letter in R to emit only a letters or nothing. This rules out a and z in R. Odd inputs would then also be unary by the second sweep. Thus R is even, and its first lane emits exactly one a, forcing b → a and one b among erasers on that lane.

Let T be the output of the other lane. T consists of R packets from a, standalone a letters from b, and e letters from z. On large odd inputs the third sweep must encounter b in T to emit a. These b letters come only from R packets, so R contains an a. If T were odd, successive interior T copies would be read on both lanes, selecting such an a and emitting a copy of R with a non-a letter. Hence T is even. Its odd lane must emit exactly three a letters. It enters every R packet on the clean lane, since the other lane of R contains a. There are exactly three R packets, each at an odd offset. All standalone a letters in T lie on its even lane.

Write q for the number of standalone a letters in T. The even lane of T emits exactly three T tokens and q copies of R in some order. Its odd lane emits AAA. For an L-sweep program choose m divisible by 2^L. Odd-width repeat units can be processed two at a time at every sweep, so across the periodic block exactly half of any A tokens are selected. Only A has odd width.

If q is positive, a mixed token word stays mixed. When A and another type occur, the selected A tokens emit R, and every other type emits some non-R token on either lane. When just R and T occur they see the same lane: the outputs are A and a mixed word on lane zero, or T and AAA on lane one. Nor can a mixed word spell a pure power of R. Counting literal b letters assigns one R copy per R token and three per T. Counting literal a letters then leaves an excess of one per A token and q per T.

If q is zero, every state reachable from homogeneous R is already homogeneous. T has additional e padding to put its first R at an odd offset, so a power of T cannot equal a power of R by b count and length. In either case any successful return to R stays homogeneous and changes multiplicity only by factors of 1, 3 or one half. No such product equals two.

## Scope and verification

The result allows arbitrary lane schedules of any fixed length. It leaves other return timings and mixed register encodings open. Run python3 -B delayed_eraser_collatz.py for 999 literal first returns and a search over 108 mixed encodings of two to four tokens. For this example none has both exact scaling operations through eight sweeps.
