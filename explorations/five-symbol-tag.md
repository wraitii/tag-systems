# Five-symbol 2-tag systems

A fixed five-symbol writer can prepare two related data runs, use them to reload its control, and read back a payload on one finite queue. For every height h ≥ 5, readback takes **16h+65 sweeps**. One additional seed of three units lets the retained payload control a second loading operation. For any independently chosen j ≥ 6, the same seed positions at that height give a second load at **16h+8j+146 sweeps**. The payload encodes j. Both loads occur on one uninterrupted queue. Generating a recurring simulation from live output remains open. Neither five-symbol universality nor a minimum alphabet size has been established here.

## The two rule tables

A tag step reads the first symbol, deletes two symbols and appends the word assigned to the symbol read. The empty word is ε. A sweep processes alternate letters of the word at its start. An odd-length word carries a one-letter cut into the next sweep. A **round** is two sweeps. Powers of words denote literal repetitions.

| Symbol | Writer table | Arithmetic clock table |
|---|---|---|
| I | `IIe` | `ezII` |
| J | `JJeb` | outside alphabet |
| z | outside alphabet | `e` |
| e | ε | ε |
| a | `b` | `b` |
| b | `aaaeaeae` | `aaazazae` |

The writer uses C = `IIe`, V = `JJeb` and W = `aaaeaeae`. The arithmetic clock uses integrator cells and a different counter unit. Its live zero test selects instructions while preserving an unread tail. Composing these two tables would require a separate simulation.

## Results and proofs

| Result | Where to find the construction |
|---|---|
| Complete writer trajectory | [Bounded seeds prepare both counts](#companion-preparation), then [the two-writer reader](#companion-reader) consumes h−2 digits. [Payload-controlled reload](#payload-controlled-reload) uses that quotient to reach the loader again. |
| Writing and branching | [Binary writing and feedback](#binary-writing) establishes the lane equations. [Instruction return](#instruction-return) shows two branches rejoining the same continuation. |
| Regenerating control | [Autonomous reloads](#autonomous-reloads) proves erasure of the original control and two transfers back into control. [Limits of the original reload](#reload-limits) gives the transfer-time lower bound. |
| Arithmetic with a clock | [Counter transfer and cycles](#arithmetic-transfer), [counted addition](#counted-addition), [instruction dispatch](#arithmetic-dispatch) and [conditional control](#conditional-control) give the entry conditions and return identities. |
| Related alphabet sizes | The [four-symbol shuttle](autonomous-loops.md) uses the writer's rules with J omitted. The [six-symbol construction](six-symbol-tag.md) uses exact queue repetition as its halt signal. |

For the end-to-end writer certificate, run `python3 -B five_symbol_prepare_companion.py`. The proof covers arbitrary heights. The verifier also compares the entire queue with the literal productions after every sweep at h=5. [Preparation verifier](five_symbol_prepare_companion.py)

## Writer constructions

### Binary writing

The two read lanes of C both emit C. Lane zero of V emits V; lane one emits VW. The two lanes of W emit `bbbb` and `b`. Thus V can write a fresh W next to a data block. The four productions other than J also implement the [autonomous shuttle and exact-cycle predicate](autonomous-loops.md).

#### Write loop

Use the queue

    C W^L C V W^M C W^R

with initial alignment zero. Exponents here are raw copy counts, including zero. More generally, an alignment p means to remove the first p letters from the indicated complete word. One round is two sweeps. Positions of the three copies of C and the single copy of V are fixed in the block encoding for all input sizes.

At alignment zero the first sweep produces, before accounting for the one-letter cut,

    C b^L C V b^(4M) C b^R.

The second sweep enters at lane one. After passing the first C it reads the even-indexed positions of the left b-run. It therefore emits ceil(L/2) units from that run. The next C reverses alignment again, so V writes one W exactly when L is even. The middle b-run emits 2M units on either lane. If L and R have equal parity, the right run emits floor(R/2) units and the round restores alignment zero. The transition is

    (L, M, R) → (ceil(L/2), 2M + 1 − (R mod 2), floor(R/2)).

Set L = 2^h − R and choose 0 ≤ R < 2^h. Each of the first h rounds halves the sum of the outside runs, so the equal-parity condition holds on every one of them. The right run supplies the digits of R least significant first. After h rounds the outside counts are 1 and 0 and the middle count is

    U = 2^h M_initial + 2^h − 1 − reverse_h(R),

where reverse_h reverses exactly h bits including leading zeroes. A blank middle block therefore receives the bitwise complement of the reversed source, in width h. An existing middle value receives those bits as a suffix. The left block is part of the input encoding and must be initialized as specified.

#### Readback and feedback

At the next round only the left b-run has odd length. V writes zero additional units, the middle count doubles to 2U, and alignment changes to one. For a read-phase boundary write

    C W^L C V b^s W^m C

with the first letter removed. The extra b-run records the intermediate symbols produced by the writer and is initially empty. For even s, a round takes this to the full word with parameters

    L' = 2L,     s' = 4+2s,     m' = ceil(m/2),     p' = 1 XOR (m mod 2),

with the first p' letters removed. To verify the middle terms, the first sweep emits one W from V and s/2 units from the even b-run, followed by m copies of b from the sparse lane of W. On the second sweep the first 1+s/2 units emit 4+2s copies of b. The run of m copies of b rounds up. Its parity determines the alignment at the next boundary.

The first read round strips the known appended zero and exposes U, with L=2, s=4. For U>0 the machine then performs one read round per trailing zero and one more round for the first one. That one selects alignment zero. The following round actually writes a W ahead of the residual b-run, halves the even left count and doubles the residual W count. For U=0 the read phase continues indefinitely and the left count doubles every round. No external clock or intervention selects between these outcomes.

For example, a blank middle block and source 010 produce 101. Its low one switches immediately after the known zero. Source 110 produces 100, so two further zero reads precede the switch. Source 111 produces zero and stays in the read loop.

#### Verification and scope

Run `python3 -B five_symbol_writer.py`. The [verifier](five_symbol_writer.py) checks all 511 width/input pairs through width eight, both readback outcomes and the first subsequent write where applicable. It executes literal individual tag steps for widths up to three and compares whole physical words as repeated literal tiles for the larger examples, including width 1,000. The lane identities above establish the formulas for all widths.

The feedback proof ends after the selected write round. That boundary includes an additional W before the remaining b-run. The [return construction](#instruction-return) continues a family of these queues into a reusable instruction boundary. It gives two composable writes and a branch on written data with a common continuation. No universality or minimality claim follows from the transducer.

### Instruction return

The following boundary denotes a **whole queue**, starting at its first letter.

    A(n,r) = C C V W^7 b^2 W^n C W^r

The mixed run left by the feedback event becomes part of the instruction boundary. The count n holds written data. The count r supplies instructions, low bits first. A round is two sweeps. All parameters below are nonnegative integers.

#### Entry and writing

Start from `C W^14 C V C W^(2+32r)`, with an empty block after V. Four rounds of the original writer produce 11 there (source 2 at width four), leaving one W on the left and 2r on the right. Six more rounds reach A(12,2r). Seven more reach A(40,r). Thus every instruction stream is accessible from an empty output in 17 rounds. The high bits of the initial right run carry the continuation through the original readback.

For any n divisible by four, the following instructions compose in arbitrary order.

| Queue | Rounds | Next queue |
|---|---:|---|
| A(n,2t) | 7 | A(2n+16,t) |
| A(n,8t+1) | 11 | A(8n+28,t) |

The two results are distinguishable from n alone. The first is 0 modulo 8 and the second is 4 modulo 8. The two affine maps are injective. Reading the residue and inverting the corresponding map recovers the preceding data value.

The first identity also applies to the unmodified handoff with no continuation. For example, width four and source 2 reach A(12,0) in ten rounds. Thereafter the data count doubles and gains 16 every seven rounds. This solves a restricted return problem and identifies a family where the right run stays empty forever.

#### A branch on the written data with a common continuation

Put the same 15-bit field 731 at the head of the stream in both cases, so r = 32768t+731. The eventual dispatch boundary exposes precisely t.

| Input n | First certified boundary (round) | Boundary exposing t (round) |
|---|---|---|
| 128x+96 | A(256x+524,16384t+364) (47) | A(4194304x+9574736,t) (215) |
| 16x+12 | A(524288x+224,t) (65) | Same boundary (65) |

The first arm executes further instructions inside the field. Its round-47 residual stream is even and therefore immediately takes the seven-round write instruction. Both arms retain x in the output. Any following write instruction can execute on either result.

For an end-to-end example, let F = 32768t+731. In the blank-output entry above choose r = 2F or r = 8F+1. The first write takes A(40,2F) to A(96,F). The other takes A(40,8F+1) to A(348,F). At this point the clock, the mixed prefix and the entire unread stream agree. The written multiplicity alone selects the branch. After 239 or 93 rounds from the initial queue, respectively, the machine reaches A(9574736,t) or A(11010272,t). Setting t to another instruction runs it without modifying the queue.

#### Proof and verification

The [executable certificate](five_symbol_writer_return.py) represents every multiplicity as c+ux+vy with x,y independent and nonnegative. A sweep enters C on either lane, emits C and flips the lane. V emits V or VW and preserves the lane. A run of m copies of W emits 4m or m copies of b and preserves the lane. A run of m copies of b entered on lane p emits floor((m+1−p)/2) copies of W and flips the lane exactly when m is odd. The final lane is the leading cut on the next queue. Each queue begins with C, so the one-letter cut always has its usual physical interpretation.

At each division the certificate requires that both variable coefficients be even. The constant term then determines the entire lane sequence for all parameter values, including a zero-length run. Induction on sweeps gives the claimed equalities of physical words. Run `python3 -B five_symbol_writer_return.py` for the symbolic identities and literal tag-step comparisons on small witnesses.

#### Limit for this encoding

The two writes and the joined branch consume one, three and fifteen bits of r. With r = 0, the seven-round instruction runs forever. More generally, while the final C is followed solely by a run of W, its two-sweep update can only double that multiplicity or halve it with rounding. For a positive multiplicity, doubling and exact halving preserve its largest odd divisor. Rounding an odd value greater than one strictly decreases that divisor. Zero stays zero. This limits using the same isolated suffix to replenish an arbitrary instruction stream. A universal simulation would need a further mechanism, for example a trajectory that makes generated data repeatedly select instructions after the supplied stream is exhausted.

### Autonomous reloads

The same five productions can erase their original control run, refill it from a separate data run, and refill it a second time from a value written during execution. The number of write laps between reloads can be any h ≥ 3. Everything runs from one initial queue.

Use C = `IIe`, V = `JJeb`, W = `aaaeaeae` and the [original productions](#binary-writing). All times below count **single sweeps**. To form Q(S,n,s), concatenate the following word and remove its first letter.

    C V S C V W b^3 W^n b^s

S is the data after the first writer. The second writer has a data run of n copies of W and a terminal control run of s copies of b. A run of length zero is empty.

#### First reload

For every x ≥ 0, start with Q(empty,13+32x,1393). The original control count 1393 is constant across all inputs.

| Sweeps from entry | S, as successive pairs of W and b counts | n | s |
|---:|---|---:|---:|
| 0 | empty | 13+32x | 1393 |
| 16 | (2,4), (8,16) | 213+512x | 88 |
| 71 | (10,72), (36,512), (16,2048), (448,90112) | 68 | 1+x |

The descendants of the original terminal run disappear on sweep 63. At sweep 71 the entire dependence on x is in the new terminal run. An odd number of sweeps can transfer this information because W produces b's and a selected b produces W. The two inputs x=0 and x=1 then take different outgoing alignments on the very next sweep.

#### The instruction executed after reloading

Write 4S for the word obtained by multiplying **each run count** in S by four. If each b-run in S has even length, then for n,k ≥ 0,

    Q(S,n,4k+1)  →  Q(W^2 b^4 (4S), 4n+1, k+1)       [8 sweeps]

A lap consumes a base-four digit of s−1, adds a new pair of runs to S, and appends a base-four one to n. In particular s=1 selects this lap forever, creating arbitrarily many distinct runs from a single finite queue. For s=1+125·4^h it executes exactly h consecutive such laps before s=126 selects a different path. During these h laps the data run starts at 68, independently of h.

#### Second reload

Set x=125·4^h in the original queue, for any h ≥ 3. At sweep 71+8h the data count is

    N = 68·4^h + (4^h−1)/3.

The terminal count is now the fixed 126. Another 81 sweeps return to Q with data count 13 and **terminal count (N+251)/16**. The low bits of that count select another eight-sweep write lap. Thus a value grown from the fixed seed 68 supplies control after the first reloaded count has reached its exit. For h=3 the successive terminal counts at these boundaries are 8001, 126, 289 and 73, starting at sweep 71.

The whole-word identity behind the 81-sweep step is as follows. Let the first three pairs of S be (2,4), (8,16), (32,64), followed by any sequence T of pairs whose counts are multiples of 64. Start with n=21+32u and s=126. The result has n=13 and s=17+2u. Its new bank begins with the pairs

    (2,12), (8,57880), (4,16384), (4,131072), (32,524288), (128,2097152)

and then W^512. Each remaining input pair W^a b^d in T contributes b^(65536a) W^(8d), in order. These b-runs all have even length. The preceding h laps produce exactly the required three pairs, a qualifying T and N ≡ 21 modulo 32. Also N ≡ 21 modulo 64 for h ≥ 3, giving (N+251)/16 ≡ 1 modulo 4.

#### Certificate

The [verifier](five_symbol_writer_reload.py) uses the literal tile identities and affine sweep routine from the [earlier return](#instruction-return). The parity of each intermediate count is checked before division. The eight-sweep identity and the 81-sweep identity each have two checks. The first carries the variable registers on an empty remainder. The second inserts one pair with independent variable counts and zero constant terms at precisely the remainder boundary. Every intermediate b count contributed by that pair is even, so inserting it preserves all later lanes on every sweep. This proves the same transformation for any finite concatenation of such pairs. The argument also allows an unpaired W at the end of the bank in the eight-sweep identity by setting the final b multiplicity to zero.

Run `python3 -B five_symbol_writer_reload.py`. It also tracks the original terminal run up to deletion, executes individual tag steps through the first reload for x=0, and checks uninterrupted whole queues through both reloads and the following lap at h=3,4,8,31.

The construction establishes two transfers back into control, separated by an unbounded number of writes. A trajectory with arbitrarily many such reloads on the same finite seed, with enough control to simulate a universal machine, remains open.

### Reload limits

A bounded reload of the growing data run cannot restart an arbitrarily long finite countdown in the same encoding. The obstruction applies even when the left bank chooses the reload path. There is a separate positive result: the reloaded value contains an arbitrarily long sequence of binary instructions that the four-symbol dispatcher can execute under the same productions. The companion reader below gives a read phase within the two-writer layout.

#### What happens after the certified reload

Let h ≥ 3 be the number of write laps before the 81-sweep reload. The [whole-queue identities](#autonomous-reloads) give data N and new terminal count s:

    N = (205·4^h − 1)/3
    s = (N + 251)/16 = (205·4^(h−2) + 47)/3.

One eight-sweep lap is available for s ≡ 1 modulo 4 and sends s−1 to (s−1)/4. For s>1, the number of consecutive applications of this instruction is therefore the largest j for which 4^j divides s−1. The bank satisfies the even-b-run condition after the reload and after each lap. Now

    3(s−1) = 205·4^(h−2) + 44.

At h=3 the right side is 864, divisible by 4² but not 4³. The terminal counts are 289, 73, 19. At h ≥ 4 the first term is divisible by 16 and 44 is divisible by 4 but not 16. Exactly one lap executes. This counts consecutive applications of the specified instruction. The queue continues on the exit path.

#### Why changing the reload constant is insufficient

Start at the write-loop exit with terminal count 126, fixed right-hand header, and data

    N_h = ((3n₀+1)·4^h − 1)/3.

This permits any nonnegative seed n₀ and any left bank. Fix a sweep budget K independent of h. For all sufficiently large h, if the queue returns within K sweeps to the same Q interface, its next **finite** sequence of eight-sweep write laps has a length bounded independently of h and n₀. The exceptional count s=1 gives the known infinite single-instruction loop.

To prove this, follow the part of the queue downstream of the last V. The left bank supplies an incoming lane bit on each sweep. Its physical letters cannot pass the persistent V into this segment. On a fixed path, W of multiplicity m emits b of multiplicity m or 4m. A b-run emits W of multiplicity (m+δ)/2, where fixing its parity and incoming lane fixes δ in {−1,0,1}. The writer adds at most one W per sweep.

The multiplicity depending on N_h has at most one descendant run at every step. A homogeneous run emits a homogeneous run, so it can merge with a neighbor or vanish, but cannot split. By induction any terminal count that still depends on N_h has the form

    F(N_h) = 2^j N_h + c

for an integer j and a dyadic rational c (an integer divided by a power of two). All other terminal counts are constants on that path. There are only finitely many paths within K sweeps. The right segment starts with a fixed number of runs and gains at most one per sweep, even if the left bank is arbitrarily long.

Choose d ≥ 0 so that 2^d c is integral and d+j ≥ 0. Then

    3·2^d (F(N_h)−1)
        = 2^(d+j) (3n₀+1)·4^h + B,
    B   = 3·2^d (c−1) − 2^(d+j).

B is nonzero: modulo three it is the negative of a power of two. For all sufficiently large h, the first term is divisible by a higher power of two than B. Their sum is divisible by exactly the same power of two as B. This bounds the number of following laps on each path, hence on their finite union. The threshold on h matters. At bounded h, uniformity in arbitrary n₀ can fail because one can encode a long countdown in n₀ itself.

A coarse bound makes the physical cost explicit. After t sweeps there are at most 4+t data runs to the right of the last V. Set N_h formally to zero in their affine expressions and let A_t be the sum of the absolute values of the resulting constants. Initially A₀=130. The lane rules give

    A_(t+1) ≤ 4 A_t + 1 + (4+t)/2.

Here 1 allows for the writer emission, and a halving changes its constant by at most one half from exact division. Merging cannot increase the sum of absolute values. Summing the geometric series gives A_t ≤ 132·4^t. After at most K sweeps every denominator divides 2^K and −K ≤ j ≤ 2K. Take d=K above. Then |B| < 401·2^(3K) < 2^(3K+9). When 2h ≥ 3K+9 the first term is divisible by 2^(3K+9). Consequently the power of two dividing F(N_h)−1 has exponent at most 2K+8, allowing at most K+4 consecutive finite laps. A constant terminal count other than 1 obeys the same bound directly from A_t. In particular, regenerating at least h finite laps from a height-h write requires **at least (2h−9)/3 sweeps of transfer time** for h ≥ 3. The constants are conservative.

Equivalently, the write recurrence n ↦ 4n+1 has formal fixed point −1/3, while this reader divides the distance from the integer 1. A fixed reload would have to send −1/3 to 1 to preserve arbitrarily many low zero bits of s−1. No map 2^j n+c with dyadic c does so. This argument leaves room for an unbounded-time transfer, two active source runs that later merge, or a different reader.

#### A reader matched to the output

Put k=h−2. A direct rearrangement gives

    s = 68·4^k + (4^k−1)/3 + 16.

For k ≥ 3 its low k base-four digits are all ones except for a two at position 2, counting from zero at the least significant digit. The unread quotient after those k digits is exactly 68. Each digit contains one zero and one one in binary.

The [four-symbol dispatcher](autonomous-loops.md) already reads an unmodified nonnegative integer M least significant bit first. Its boundary D(b,M) has a timing counter with exponent b. An odd bit takes one two-sweep round and increments b by one. An even bit takes 2b+5 rounds and increments b by two. Consequently a base-four one costs 2b+8 rounds (odd, even), and a base-four two costs 2b+6 rounds (even, odd). Either increases b by three and leaves the quotient after division by four. Summing proves the physical reader identity for b ≥ 0 and h ≥ 5:

    D(b,s) → D(b+3k,68)
    elapsed two-sweep rounds = k(2b+8) + 3k(k−1) − 2.

For example, h=5 gives s=4389 with low base-four digits 1,1,2 in read order. From D(0,4389) these take 40 rounds and reach D(9,68). The [verifier](five_symbol_writer_reload.py) checks the lap counts and exercises the physical reader.

This identifies what a compatible read phase can compute: it recovers the generated length k in a live counter and retains a fixed continuation. The identity starts from the dispatcher's queue encoding. The actual reload boundary contains two persistent writer cells V, whereas D contains none. Each V emits another V on either lane, so reaching literal D by simply waiting for those markers to disappear is impossible at these sweep boundaries.

### Companion reader

The 81-sweep reload and a reader can now run consecutively in one physical queue with the original five productions. The construction requires a second data run at the **input** to that reload. It reads an arbitrary number of generated digits and keeps their quotient. The original, single-run input enters a different regime in which its terminal run doubles forever for every height h ≥ 11.

Use C = `IIe`, V = `JJeb`, W = `aaaeaeae`. Times below count single sweeps. The following words have their first letter removed, as in the [original reload proof](#autonomous-reloads).

#### Choosing the second count

Put k=h−2 ≥ 3. The original data count N and reloaded count s satisfy

    s = (N+251)/16 = (205·4^k+47)/3.

A write lap divides the distance of its control count from 1 by four. Set the companion to u=2s−46. Then s+u−1=205·4^k, so the sum has exactly k laps available. Two b-runs separated by a W-run let the clock act on this sum while retaining each count individually.

At entry to the modified reload the physical word is

    C V S C V W b^3 W^N b^131072 W^(2N−234) b^126.

The original bank S is permitted unchanged. Relative to the original entry, the two extra runs are immediately before the terminal control field. After 81 sweeps the word is

    C V S' C V W b^3 W^13 b^s W^64 b^(2s−46).

Here S' is exactly the bank produced by the original reload. To verify the new suffix generically, write N=21+32x and allow the added W-run to have any count 32y. The three output counts after W^13 are 17+2x, 64, and 2y. Substituting 32y=2N−234 gives the claimed companion since N ≡ 21 modulo 32. The original symbolic insertion argument for the arbitrary remainder of S applies unchanged: the new suffix preserves the boundary cut on the entire 81-sweep itinerary. This last parity statement also follows by setting y=0 and following the added separator and variable run: both contribute even width on each intermediate sweep.

#### Reading the two runs

Consider the same boundary with right-hand suffix `W b^3 W^n b^L W^m b^R`. The three rows below are the only residue cases needed. They take eight sweeps each, for L,R ≥ 8. Write 4S for multiplying every run count in S by four. The bank becomes `W^2 b^4 (4S)` and the data count becomes 4n+1.

| L mod 4 | R mod 4 | Spacer before | Spacer after | New L and R |
|---:|---:|---:|---:|---|
| 1 | 0 | 64 | 16 | ceil(L/4), ceil(R/4) |
| 2 | 3 | 16 | 16 | ceil(L/4), ceil(R/4) |
| 3 | 2 | 16 | 16 | ceil(L/4), ceil(R/4) |

The spacer keeps the runs separate. It has even physical width on every sweep of these identities, so the downstream alignment sees the same combined parity as in the unsplit lap. On a b sweep, selecting alternating letters across both b-runs therefore emits the same total number of W units as selecting across their concatenation. On a W sweep, their images use the same lane. Tracking the individual counts gives the rounding and spacer sizes in the table. The [verifier](five_symbol_companion_reader.py) checks each row on arbitrary affine counts and compares the full literal tag queue after every sweep on small inputs. The bank may have any even b-run counts by the original eight-sweep insertion identity.

On each row L−1 and R−1 undergo ordinary floor division by four. The low k base-four digits of s−1, in read order, are 0, 1, 2 and then ones: expand s=68·4^k+(4^k−1)/3+16. Hence L has residue 1 on the first lap, 3 on the third, and 2 on every other lap. The sum supplies the complementary R residue each time. By induction all k laps execute.

After **81+8k sweeps** from modified reload entry the physical counts are L=69, m=16 and R=137. Thus the unread quotient in the L−1 convention is **68**. The new data count is (40·4^k−1)/3 and the bank has k newly written pairs. The combined control is 206, which exits this sequence of laps. Neither h nor an external clock is consulted during execution.

#### Fate of the unmodified trajectory

There is an invariant family of phase-zero queues consisting of two sections of the form `C V W b^(2a+1) P`, where every b-run in P has even count. Take P empty or beginning with W, with a separate a and P in each section. Each section enters on lane zero and passes lane zero. The first sweep sends its leading part to `C V W b W^a`. Its remainder is on lane zero, mapping W^d to b^(4d) and b^d to W^(d/2). The second sweep therefore returns the leading part to `C V W b^(4a+1)` and doubles every run in P. This equality also holds when neighboring runs coalesce. The section is again in the family.

For every h ≥ 11 the actual original queue reaches this family **334 sweeps after the second reload**. The finite entrance certificate uses the bank prefix shared by all those h. The reloaded control is s₁₁+205·4^9 x, where x=(4^(h−11)−1)/3 and s₁₁=(205·4^9+47)/3. Each later pair in the bank has the form b^(2·4^11·65536 y) W^(32·4^11 z). The verifier follows the variable control through 334 sweeps and checks the invariant on the full output. It separately inserts one zero-constant pair with independent y,z at the shared bank boundary. Its intermediate b-width contributions are even throughout, so any number of such pairs preserves the same itinerary. The original rightmost run at entrance to the invariant family is b^(544+1640x). It doubles every two sweeps thereafter. This establishes the eventual behavior of the original family without extrapolating from observed heights.

The bounded-seed preparation below supplies both input runs at the loader boundary.

### Companion preparation

For every h ≥ 5, one finite queue under the original five productions prepares both W^N and W^(2N−234), merges the companion into position, executes the 81-sweep reload and reads h−2 digits. Here N=(205·4^h−1)/3. No initial data run has multiplicity N or 2N−234. The input specifies h through the number and spacing of bounded seeds.

#### Initial queue

Use the C, V and W tiles of the [companion reader](#companion-reader). Remove the first letter from the following word. Begin with `C V C V W b^3 W^68`. The first writer's bank is empty. After this prefix put a total of T=131197·4^h+1 copies of b. Interrupt that b-run with W seeds as follows. Positions count only b letters, from the beginning of this final run.

* For each i from ceil(h/2) to h−1 inclusive, insert one W-run after Bᵢ=131071·4^h+4^i copies of b.
* The first inserted run has count 1952 for even h and 2128 for odd h. Every later run has count 2050.

There are floor(h/2) seeds. The data counts are bounded independently of h. The b gaps grow with h and are part of the input; this construction does not generate that timing layout from the previous blank-writer entry.

#### How an inserted run moves

Use the eight-sweep write lap, with T ≡ 1 modulo four. Consider a W-run after the first B of those b letters. For the two residues used in preparation, the following identities hold. B and T−B are at least eight.

| B mod 4 | Initial W count | Final W count | Final position in the b-run |
|---:|---:|---:|---:|
| 0 | m ≥ 1 | 4m | B/4 |
| 1 | 4m, m ≥ 1 | m | (B+3)/4 |

In both cases the total number of b letters becomes (T+3)/4. The bank gains the pair W² b⁴ ahead of its old runs with all counts quadrupled, and the primary data count goes from n to 4n+1.

These are single-insertion sweep identities. To use several insertions at once, follow their descendants as labeled subruns. Each insertion has even physical width at every intermediate sweep. Deleting it leaves the entering lane of every other subrun unchanged. An interrupted run of b's therefore emits the same total number of W units as before, and an interrupted W-run likewise emits the same number of b's. Each labeled insertion follows its single-insertion trajectory. If two positions coincide, the two adjacent W-runs physically merge. The labels can still be used in the proof because both contributions have even width on the intermediate b sweeps. The [verifier](five_symbol_prepare_companion.py) checks the lane identities with variable positions and seed counts; the variable count coefficients would fail its parity check if an inserted run introduced an odd b width.

#### Why the counts add up

After j laps the position is ceil(Bᵢ/4^j). During the first i laps it is divisible by four at entry, so the seed grows by four on each lap. During the remaining h−i laps the position at entry equals 131071·4^(h−j)+1. It now shrinks by four on each lap. Since i ≥ ceil(h/2), every required division is exact. All seeds end at position **131072**, with the seed of initial count mᵢ contributing mᵢ·4^(2i−h). The terminal b count after this position is 126. Meanwhile the fixed starting value 68 has grown to N.

Write l=floor(h/2). For even h the sum of the contributions is 2050·(16^l−1)/15−98; for odd h it is 4·[2050·(16^l−1)/15+78]. These are both (410·4^h−704)/3 = **2N−234**. The corrections −98 and +78 explain the first seed counts. For example, h=5 starts with just two seeds, of counts 2128 and 2050. They contribute 8512 and 131200, respectively. Their sum is 139712, while the primary count is 69973.

Consequently the complete suffix at sweep 8h is exactly

    W b^3 W^N b^131072 W^(2N−234) b^126.

The first bank holds the h generated pairs, newest first, with counts (2·4^j,4·4^j) for j=0,…,h−1. This is an admissible bank for the 81-sweep loader, including its first three required pairs. The companion-reader identities now apply to the actual queue. After another 81+8(h−2) sweeps the two b counts are 69 and 137, separated by W^16. The unread quotient is 68. Total time from the seed queue is **16h+65 sweeps**.

#### A lower bound on the seeds

The required companion (410·4^h−704)/3 has exactly **h one-bits**. In base four its digits are `2020`, followed by h−5 copies of `2`, followed by `13000`. The formula gives these digits directly at h=5, and increasing h multiplies the count by four and adds 704, which inserts another `2` before the fixed suffix.

Label each initial W seed after the primary run. A homogeneous labeled piece stays homogeneous, even if it touches another piece of the same type. Its count can be multiplied by four, left alone, or halved with either rounding. Each operation preserves or decreases binary popcount. For rounding an odd 2u+1 upward, popcount(u+1) ≤ popcount(u)+1 = popcount(2u+1). Adding counts when labels physically merge can only lose further one-bits to carries.

Suppose the companion is required at an even sweep with a surviving descendant of the initial primary between it and the last writer, as in this construction. Writer emissions stay upstream of that descendant. Initial b gaps have b descendants at even sweeps. Hence every W in the companion comes from a labeled W seed, regardless of the intervening lanes or seed positions. Their initial popcounts must sum to at least h. In particular a bound of 2128 per seed requires at least ceil(h/11) seeds, since 2047 is the smallest integer with eleven one-bits and 4095 the smallest with twelve. At odd heights the given construction attains the popcount bound exactly: 2128 has three one-bits and 2050 has two. A recurring construction using this same ordered interface would have to supply that growing amount of data in the seeds or relax the bound on their sizes.

#### Independent payload and verification

One can replace the starting 68 by 68+4x for arbitrary x ≥ 0 without changing any seed or gap. This increases the primary loader input by 4x·4^h and the first reloaded b count by 4x·4^(h−2). Its low h−2 digits in the reader convention are unchanged. Reading therefore ends at 69+4x and 137, retaining quotient 68+4x. Their sum is 206+4x and exits the write lap. The exact target relation 2N−234 above is for x=0; this extension demonstrates that independent payload survives the same program.

Run `python3 -B five_symbol_prepare_companion.py`. It checks the single-seed identities symbolically, compares the entire physical word to the literal productions after every sweep at h=5, and checks the merged and final queues through h=64 with a symbolic payload. The induction proves the result at arbitrary height.

At this boundary the retained quotient can control another loading operation if the preparation includes one further bounded seed, as shown below.

### Payload-controlled reload

At the original reader exit the combined control is 206+4x. To make the next instruction depend on the retained payload, add exactly three W tiles at position **131072·4^h** in the initial terminal b-run. Positions still count only b letters. This is beyond every original seed. Keep the initial primary count 68+4x.

The new position is divisible by four on entry to every one of the h preparation laps. The zero-residue insertion identity quadruples the new seed on every lap. It joins the other seeds at position 131072, increasing the companion by 3·4^h. The first loader divides this increment by 16. The k=h−2 reader laps divide it by another 4^k, on the same residues as before. Thus at sweep 16h+65 the right section ends in

    W b^3 W^n b^L W^m b^R,
    n = (40·4^k−1)/3,    L = 69+4x,    m = 16,    R = 140.

The combined control is now 209+4x. As long as T=L+R is 1 modulo four, an eight-sweep lap sends T−1 to (T−1)/4, writes n ↦ 4n+1, and prepends the usual record to the quadrupled bank. The right edge follows these rows in order, stopping when the total fails the residue test.

| R | m | Next R | Next m |
|---:|---:|---:|---:|
| 140 | 16 | 35 | 4 |
| 35 | 4 | 9 | 4 |
| 9 | 4 | 3 | 16 |
| 3 | 16 | 1 | 16 |
| 1 | m, a positive multiple of 16 | 1 | 4m |

For a direct lane proof set L=4u+((1−R) mod 4) in each row. Applying the tile identities eight times gives L′=ceil(L/4) and the two counts shown. The final row holds for every spacer 16+16v. Each old bank pair obeys the same insertion identity as in the preparation lap. This proves the recurrence for arbitrary u and admissible banks. In particular the number of additional laps is exactly 1+ord₄(52+x), where ord₄ counts factors of four.

**Return to the loader.** Choose j ≥ 6 independently of h and put x=125·4^(j−1)−52. Now T−1=125·4^j. Exactly j laps bring T to 126, with L=125, R=1, spacer M=4^(j−2) and data N=(40·4^(k+j)−1)/3. The bank starts with the three required records and every later run has multiplicity divisible by 64. The spacer lies inside the terminal control, immediately before its last b. Its contribution survives the loader.

Indeed take any N=21+32u and M=256v in this split terminal block. After 81 sweeps the bank is the ordinary loader output, the data is 13 and there is a **single** terminal b-run of length

    17+2u+4v = (N+251)/16 + M/64.

The symbolic sweep certificate propagates u and v independently across all 81 sweeps. Putting v=0 recovers the unsplit loader. The old bank remainder can be inserted on the established parity path because its intermediate b widths are even. Our N and M satisfy these congruences for every j ≥ 6. This gives the second load at sweep **16h+8j+146**. For example h=5 and j=6 give x=127948, N=3495253, M=256 and terminal count 218473 at sweep 274.

**Long reloads eventually double.** For j ≥ 14 the queue reaches the [doubling region](#fate-of-the-unmodified-trajectory) 334 sweeps after this second load. To check the entrance, write the terminal count as (40·4^(k+j−2)+47)/3 + 4^(j−5). Its difference from (205·4^9+47)/3 is a nonnegative multiple of 4^9. The 334-sweep certificate accepts every such increment 4^9 w and leaves a final run of 544+8w copies of b. The first eleven records supplied before the loader agree with that certificate. Its remaining bank pairs satisfy the required divisibilities because every later record or older bank run was multiplied by at least 4^11 before loading (older W counts are even and older b counts are multiples of four). An unpaired final run is covered by a zero partner. The terminal run doubles every two sweeps thereafter.

**Fate of the original readback.** Without the extra seed, the zero-payload family already enters the doubling region at sweep **16h+141**. More generally this holds for x=8192v. At readback n=853+2560u with u=(4^(k−3)−1)/3, and L=69+32768v. Keep the first three records. Every remaining W count is a multiple of 128 and every remaining b count a multiple of 256. Following these two input variables for 76 sweeps gives the two required section headers with first b counts 7 and 21. The queue ends in W^(72+160u) b^(128v). Independently inserting a remainder pair W^(128a) b^(256d) transforms it to W^(131072a) b^(4096d), preserving all intermediate lanes. This proves entry for the full bank and all heights. At v=0 the final positive W-run doubles every two sweeps.

Run `python3 -B five_symbol_prepare_companion.py` and `python3 -B five_symbol_companion_reader.py`. The first verifier also compares the complete physical word with the literal productions after each of the 274 sweeps in the example. The return theorem supplies a further operation on live output. For j ≥ 14 its proved continuation instead gives unbounded doubling, so this family cannot itself implement indefinitely repeated loads.

## Arithmetic clock constructions

### Arithmetic transfer

The word emitted by `b` gives `bbbb` on lane 0 and `bee` on lane 1. A zero-decrement therefore retains its counter on second-sweep lane 0. An odd intermediate block flips the alignment downstream.

Place six integrator cells in the queue, with X just before cell 0 and Y just before cell 1. The low bit of the clock describes cell 0. At exponent x, a counter is a run of 2^x copies of the word emitted by `b`. Each cell is `ezII` prefixed with `e` if its clock bit is 1. Drop the first letter of the assembled word if the top clock bit is 1. One round is two sweeps.

**Return theorem.** For every integer k ≥ 1, exactly 168k − 5 rounds take (49, 0, 9k) to (49, 0, 25k − 3). Along this segment X fires once and Y twice. Here “fires” means that a decrement at zero regenerates the counter block.

| Stage | Rounds | Ending state (clock, X, Y) |
|---|---:|---|
| Start | 0 | (49, 0, 9k) |
| X fires | 1 | (15, 0, 9k+1) |
| Repeat the clock-15 orbit 3k−1 times | 21(3k−1) | (15, 15k−5, 4) |
| Ordinary prefix | 12 | (1, 15k+1, 0) |
| Y fires | 1 | (20, 15k+2, 0) |
| Ordinary prefix | 16 | (34, 15k, 0) |
| Y fires | 1 | (30, 15k−1, 0) |
| Repeat the clock-30 orbit 5k−1 times | 21(5k−1) | (30, 2, 25k−5) |
| Ordinary prefix | 6 | (49, 0, 25k−3) |

The per-orbit changes at clocks 15 and 30 are (+5,−3) and (−3,+5). Their componentwise minimum partial sums, including time zero, are (0,−6) and (−5,0). The last repetitions start with Y=7 and X=5 respectively, so all repetitions finish without underflow. The 12-, 16-, and 6-round prefixes have minimum partial sums (0,−4), (−2,0), and (−2,0). The verifier computes these finite certificates and checks the three exceptional transitions.

**Composition.** Write N=16Y−27 at the clock-49 entry. A certified return acts by N ↦ 25N/9 when Y is a positive multiple of 9. Since 16Y−27 is divisible by 9 exactly when Y is, the number of consecutive applications of this certified formula from Y ≥ 9 equals the largest m with 9^m dividing N. In particular there are inputs for every prescribed m. For example, take N=9^m d with positive d coprime to 3 and congruent to −27 times the inverse of 9^m modulo 16. This gives an integer Y=(N+27)/16. Choose d large enough that Y ≥ 9. No integer Y makes N zero. Other itineraries after this formula ceases to apply require separate analysis.

**An exact cycle using both zero events.** With the same five productions, use five cells and put X and Y before cells 0 and 2. The rounds are (5,0,0) → (29,1,0) → (19,0,1) → (5,0,0). Y fires on the first round and X on the third. The final encoded queue equals the starting queue exactly. This uses a different layout from the arithmetic return.

**Clock restriction.** Consider n ≥ 2 integrator cells and a stretch with no underflows. If s is the current clock and d its successor after one sweep, then d₀=s₀+sₙ₋₁ and dⱼ=sⱼ+dⱼ₋₁ over the binary field. For an eigenvalue t the equations are (t+1)s₀=sₙ₋₁ and (t+1)sⱼ=t sⱼ₋₁. Taking the determinant of these cyclic bidiagonal equations gives the characteristic polynomial (t+1)^n + t^(n−1). Its constant term is 1. For even n its derivative is t^(n−2), and for odd n its derivative is (t+1)^(n−1). Neither derivative shares a root with the polynomial. The sweep matrix is therefore diagonalizable over a finite binary extension, where every nonzero element has odd multiplicative order. Squaring the matrix for a two-sweep round also gives odd order. Every complete least-period ordinary orbit has odd length, so every counter accumulates an odd, nonzero drift on that orbit. The exceptional zero events allow a route to leave one drift pattern and enter another.

The implementation checks whole physical words using repeated literal tiles. It compares each overlap for a full common tile period or its length, whichever is smaller. Small examples also run through one deletion at a time. Run `python3 -B five_symbol_transfer.py`.

**Two exact-cycle outcomes in the arithmetic layout.** Both inputs traverse the arithmetic return first. From (49,0,9), after 545 rounds both counter blocks have disappeared and the clock is 36. Another 21 rounds reproduce the identical physical queue. From (49,0,18), after 659 rounds only X remains, at exponent 81 and clock 63. The 21-round ordinary orbit from clock 63 changes X by +5 and its minimum prefix change is −1. Thus every subsequent lap is valid and the physical lengths are unbounded. A deterministic queue that ever repeats has bounded future length. These are a cycle and a noncycle from the same placement, established without changing the stopping convention. The verifier treats a lost block as absent on later rounds and checks these finite trajectories directly against physical words.

### Counted addition

Keep the productions of [the transfer construction](#arithmetic-transfer), including `I → ezII` and `b → aaazazae`. Use five integrator cells and put counter blocks before cells 0, 1, 2 and 4. In this section tuples list the clock followed by the four **multiplicities** of `aaazazae`. The first cell is the low clock bit, and the top bit sets the usual one-letter boundary cut.

For any multiple x of four and any positive y, two-sweep rounds give

    (21, x,   y, 1, 1)
    (20, x/2, 2y, 2, 1)
    (14, x/4, y, 1, 2)
    (21, x/2, 2y, 1, 1).

Start with x = 22·2^h and y = 2^d, with h ≥ 0 and d ≥ 1. The three-round body runs exactly h times. Its control blocks return to multiplicity one every time. At x = 22 the intermediate odd block selects a different clock. The complete exit is

    (21, 22, y, 1, 1)
    (20, 11, 2y, 2, 1)
    (17,  5, y, 1, 2)
    (16,  2, 2y, 2, 4)
    ( 5,  1, y, 1, 2).

Here y = 2^(d+h). Thus a fixed body adds h to the output exponent and hands control to clock 5 after 3h+4 rounds, with all four blocks present. At clock 5 the recurring sequence, valid for even y and positive z, is

    ( 5, 1, y,   1, z)
    (29, 2, y/2, 1, 2z)
    (19, 1, y,   2, 4z)
    ( 5, 1, 2y,  1, 2z).

These identities follow by reading alternating letters of the displayed blocks. The two first-sweep outputs for a unit are `bbbb` and `bee`. On the next sweep a run of even multiplicity on the sparse lane halves, and an odd run rounds according to the read alignment and flips the alignment downstream. The [verifier](five_symbol_countdown.py) checks the intermediate rows against the physical queue.

### Arithmetic dispatch

The five rules and the six clock cells are those of [the arithmetic return](#arithmetic-transfer). X still precedes cell 0 and Y precedes cell 1. X starts with one copy of `aaazazae`. Give Y an arbitrary positive number M of copies. In the instruction encoding M = 4(S+1). A header with radix R and digit d represents S = Rk+d, where k is the unread tail. Headers are read least significant first.

**Why this changes the branch.** On the increment lane each copy of the counter unit emits four copies of b, giving 2M units after the second sweep. On the decrement lane each unit emits `bee`. An even M gives M/2 units. For odd M the two read lanes give (M+1)/2 and (M−1)/2 units, respectively. The odd intermediate block also flips the downstream alignment. Both rounded results are positive for odd M ≥ 3. This lets the clock branch on payload bits while keeping the block present.

#### A live guard and an independent data register

Put guard and data blocks before cells 2 and 5. Each uses the original power-of-two encoding. Write Z and D for their exponents. At each instruction boundary the clock is 49 and the X exponent is zero. Every line in this table takes a tape of size 4(Rk+d+1) to one of size 4(k+1), for every k ≥ 0 and D ≥ 1.

| R | d | Guard before | Guard after | Change in D | Rounds |
|---:|---:|---:|---:|---:|---:|
| 131072 | 28942 | 7 | 1 | +3 | 73 |
| 131072 | 28942 | Z ≥ 10 | Z−9 | +9 | 59 |
| 16384 | 16375 | 1 | 5 | +6 | 90 |
| 2048 | 445 | Z ≥ 4 | Z+1 | +15 | 81 |
| 512 | 269 | Z ≥ 4 | Z+3 | +5 | 55 |

The first header tests a live counter. At Z=7 a guard decrement at zero changes the path. At Z ≥ 10 the guard has enough units of exponent to complete the ordinary guard commands. The two paths consume the same header and preserve the entire tail. One interpretation takes Z=7+3v on input. The output is then Z=1+3 max(v−1,0), and the net data change distinguishes v=0 from v>0.

For the two guard inputs 7 and 10, the test leaves Z=1 in both cases. Appending digits 16375, 445, 445 resets Z to 7. Starting from the same tape, the complete operation takes 325 rounds and adds 39 to D for guard 7, or takes 311 rounds and adds 45 for guard 10. Each case ends with the same clock, scratch exponent, guard, and unread tail. Further tests can follow immediately. The optional digit 269 sets guard 7 to 10 for a subsequent test and adds five to D.

For an unbounded countdown, start at Z=7+9v. Repeating the test header v times decreases the guard by nine each time. One more test takes the zero route, after which the reset works. The reset certificate applies to guard 1. A uniform reset for every possible output of the biased saturating decrement is a separate problem.

#### Two instruction digits in a second layout

With just the original X and Y blocks, digits 62 and 69 in radix 128 both recover exactly 4(k+1) copies and return to clock 49. They take 49 and 41 rounds, respectively. Thus any finite word of these two digits can be chosen independently and followed by an arbitrary tail. With additional powers of two before cells 3 and 5, the exponent changes are (+1,+11) for 62 and (+1,+7) for 69. Initial exponents P ≥ 1 and Q ≥ 7 suffice for arbitrary compositions. The difference Q−7P records four per occurrence of 62.

#### Verification

The [verifier](five_symbol_dispatch.py) carries M symbolically as ak+b. At every halving it checks that a is even, so b fixes the parity for every tail. It rejects a path if the zero tail could lose the block. It checks the first return to the claimed clock and scratch state. It also compares both sweeps of the whole physical word against the predicted queue, including across a composed test and reset. For bounds on register exponents, the least allowed starting value follows the certified path without an underflow at that register. Increasing the starting value translates all of its exponents by the same amount.

These are instructions on a finite queue-encoded stream. The tested guard and updated data survive the operation, but a universal program using this dispatch has yet to be constructed.

#### Why the power-of-two search changed direction

For the original input with Y multiplicity 2^h, write h=9k+r with k≥1 and 1≤r≤8. Before the first live return to clock 49 with X exponent zero, residues 3 and 6 erase X. The other six residues erase Y. The verifier checks all eight infinite families by inserting 3(k−1) ordinary clock-15 laps into the k=1 path and 5(k−1) clock-30 laps if that second stage is reached. It verifies the minimum exponents, exceptional steps, and absence of an earlier live return inside those laps. Below h=9 the only surviving first return occurs at h=1, which reaches h=2 after 23 rounds. This obstruction is specific to the original power encoding and that entry condition.

### Conditional control

Use the five productions and six-cell clock from [the dispatch construction](#arithmetic-dispatch). At a dispatch boundary the clock is 49, the X exponent is zero, and Y contains 4(S+1) copies of `aaazazae`. Write H(w,d,k) = 2^w k+d for a w-bit instruction digit d followed by unread stream k. The guard Z and data D are exponents before cells 2 and 5. One round is two sweeps.

#### Conditional skip on an unbounded counter

Start with Z=7 and D=2+4v for any nonnegative integer v. Use **the same stream** in both cases. From the least significant end its headers are (16,65267), (9,269), (9,269), (23,4240311), followed by any k ≥ 0.

| Input | Next instruction after the 23-bit field is encountered | Rounds through recovery of k | Z at k | D at k |
|---|---|---:|---:|---:|
| v=0 | Dispatch k immediately | 339 | 16 | 29 |
| v>0 | Execute (15,16563), then dispatch k | 509 | 11 | 37+4v |

The optional instruction lies in the shared input, since 4240311 = 256·16563+183. The following are first returns to clock 49 with the scratch exponent zero.

1. At v=0, digit 65267 takes 84 rounds, leaves Z=7, and changes D from 2 to 4. The data block survives two decrements at zero. For v>0 the digit takes 166 rounds, sets Z=10, and adds six to D. At the least positive input D=6, the data block never suffers an underflow, so increasing D translates the entire positive path.
2. Each digit 269 consumes nine bits, adds three to Z and five to D, and takes 55 rounds. The resulting guards are 13 and 16.
3. At Z=13 the 23-bit digit consumes the entire field in 145 rounds. It leaves Z=16 and adds 15 to D. At Z=16 the first eight bits 183 suffice for a return in 160 rounds. The remaining stream is H(15,16563,k), with Z=10 and D increased by eight.
4. That 15-bit instruction executes in 73 rounds, leaves Z=11, adds 11 to D, and exposes k. For example, either path can immediately execute another digit 269 from k. The positive input v remains recoverable as (D−37)/4.

#### A guard that generates two executable headers

A second branch starts with H(18,180568,k), Z equal to 7 or 25, and D ≥ 3. At Z=7 it reaches (stream k, Z=2, data D+12) in 184 rounds. At Z=25 it visits the following dispatch boundaries.

| Rounds since previous boundary | Stream at boundary | Z | Data exponent |
|---:|---|---:|---:|
| 129 | H(8,255,H(15,22655,k)) | 2 | D−1 |
| 58 | H(15,22655,k) | 5 | D+5 |
| 81 | k | 2 | D+4 |

At the first boundary both branches have the same clock, scratch and guard. Their unread streams select different instructions. Taking k to start with (19,279519) makes the direct branch execute that reset while the indirect branch executes byte 255 first. Both subsequently execute the reset on the identical k, restoring Z=7 and subtracting one from D. Six digits 269 can then raise Z to 25. The verifier composes a direct branch, reset, six raises and an indirect branch on one initial stream.

#### Certificate and remaining limitation

Run `python3 -B five_symbol_control.py`. The [verifier](five_symbol_control.py) uses affine tape counts for arbitrary k, checks first returns, and compares complete physical queues using repeated literal tiles. The least permitted D on each translated path suffices because every higher D follows the same lane sequence until that register underflows. The verifier checks the two exceptional data underflows on the zero path explicitly.

These witnesses implement finite instruction sequences. An input-independent loop body supporting arbitrarily many data-controlled iterations is still needed for this approach. A restriction on the current tape encoding is that the odd part of any surviving positive block multiplicity cannot increase. Doubling or exact halving preserves it. At an odd multiplicity u>1 the rounded result is at most (u+1)/2, so its odd part strictly decreases. Generated headers can therefore change the instruction sequence, but repeatedly consuming fresh odd mantissas on the same block is a finite resource for any fixed starting queue. Exponent dynamics after that resource is exhausted remain a separate question.
