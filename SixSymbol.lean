import Std

/-!
# A six-symbol tag simulation of finite reversible counter machines

The main theorem is `SixSymbol.halt_iff_exact_cycle`. Its input word is
computed by `encode`. The running example at the end proves a cycle occurs
exactly for positive input. This file checks with Lean 4.19 and Std.
-/

namespace SixSymbol

inductive Letter where
  | I | D | z | e | a | b
  deriving DecidableEq, Repr

open Letter
abbrev Word := List Letter

def production : Letter → Word
  | I => [e,z,I,I]
  | D => [D,D,e,z]
  | z => [e]
  | e => []
  | a => [b]
  | b => [a,a,a,e,a,e,a,e]

def step : Word → Option Word
  | x :: _ :: tail => some (tail ++ production x)
  | _ => none

def lane (skip : Bool) : Word → Word
  | [] => []
  | x :: xs => (if skip then [] else production x) ++ lane (!skip) xs

def integrator (s : Bool) : Word := (if s then [e] else []) ++ production I
def differentiator (s : Bool) : Word := production D ++ (if s then [e] else [])

theorem integrator_lane (p s : Bool) :
    lane p (integrator s) = integrator (p ^^ s) := by cases p <;> cases s <;> rfl

theorem differentiator_lane (p s : Bool) :
    lane p (differentiator s) = differentiator p := by cases p <;> cases s <;> rfl

-- Clock cancellation for an arbitrary incoming bit stream. diff and sumBits
-- unfold the two cell recurrences above with zero initial state.
abbrev Stream := Nat → Bool

def diff (bits : Stream) : Stream
  | 0 => bits 0
  | n+1 => bits (n+1) ^^ bits n

def sumBits (bits : Stream) : Stream
  | 0 => bits 0
  | n+1 => bits (n+1) ^^ sumBits bits n

def bank (cell : Stream → Stream) : Nat → Stream → Stream
  | 0, bits => bits
  | n+1, bits => bank cell n (cell bits)

private theorem sum_diff (bits : Stream) : sumBits (diff bits) = bits := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((bits (n+1) ^^ bits n) ^^ sumBits (diff bits) n) = bits (n+1)
    rw [ih]
    cases bits n <;> cases bits (n+1) <;> rfl

private theorem bank_slide (cell : Stream → Stream) (n : Nat) (bits : Stream) :
    bank cell n (cell bits) = cell (bank cell n bits) := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih => exact ih (cell bits)

theorem clock_cancel (n : Nat) (bits : Stream) :
    bank sumBits n (bank diff n bits) = bits := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    change bank sumBits n (sumBits (bank diff n (diff bits))) = bits
    rw [bank_slide, ih, sum_diff]

-- A complete physical sweep. Pending letters have already been produced;
-- only the old prefix remains to be read. On an odd crossing the last old
-- letter must have a partner before its own production is appended.
def runSteps : Nat → Word → Option Word
  | 0, w => some w
  | n+1, w => (step w).bind (runSteps n)

def sweepSteps : Word → Nat
  | [] => 0
  | [_] => 1
  | _ :: _ :: xs => 1 + sweepSteps xs

def sweepFrom : Word → Word → Option Word
  | [], pending => some pending
  | [_], [] => none
  | [x], _ :: tail => some (tail ++ production x)
  | x :: _ :: xs, pending => sweepFrom xs (pending ++ production x)

theorem sweep_exact (old pending : Word) :
    runSteps (sweepSteps old) (old ++ pending) = sweepFrom old pending := by
  match old with
  | [] => rfl
  | [x] => cases pending <;> rfl
  | x :: y :: xs =>
    simpa [sweepSteps, Nat.add_comm 1, runSteps, step, sweepFrom, List.append_assoc]
      using sweep_exact xs (pending ++ production x)

-- An unconditional physical example: one W tile doubles in six literal steps.
theorem double_one : runSteps 6 (production b) = some (production b ++ production b) := rfl

def tiles (tile : Word) : Nat → Word
  | 0 => []
  | n+1 => tile ++ tiles tile n

-- Each complete W in an uncut sweep appends four b's. In the following
-- sweep, each group of four b's appends two W's, independently of pending.
private theorem dense_sweep (n : Nat) (pending : Word) :
    sweepFrom (tiles (production b) n) pending = some (pending ++ tiles [b,b,b,b] n) := by
  induction n generalizing pending with
  | zero => simp [tiles, sweepFrom]
  | succ n ih =>
    change sweepFrom (tiles (production b) n) ((((pending ++ [b]) ++ [b]) ++ [b]) ++ [b]) = _
    rw [ih]
    simp [tiles, List.append_assoc]

private theorem regenerate (n : Nat) (pending : Word) :
    sweepFrom (tiles [b,b,b,b] n) pending = some (pending ++ tiles (production b) (2*n)) := by
  induction n generalizing pending with
  | zero => simp [tiles, sweepFrom]
  | succ n ih =>
    change sweepFrom (tiles [b,b,b,b] n) ((pending ++ production b) ++ production b) = _
    rw [ih]
    simp [Nat.mul_succ, tiles, List.append_assoc]

theorem double_block (n : Nat) :
    let w := tiles (production b) n
    let mid := tiles [b,b,b,b] n
    (runSteps (sweepSteps w) w).bind (runSteps (sweepSteps mid)) =
      some (tiles (production b) (2*n)) := by
  have first := (sweep_exact (tiles (production b) n) []).trans (dense_sweep n [])
  have second := (sweep_exact (tiles [b,b,b,b] n) []).trans (regenerate n [])
  simp only [List.nil_append, List.append_nil] at first second
  dsimp only
  rw [first]
  exact second

-- Abstract exponent semantics of one two-sweep command, projected to the
-- tested register and one arbitrary passive register. none flags a missed
-- singleton or an unintended passive underflow.
structure Registers where
  tested : Nat
  passive : Nat
  cut : Bool
  deriving DecidableEq, Repr

def adjust (n : Nat) (down : Bool) := if down then n-1 else n+1

def command (s : Registers) (testDown passiveDown returnBit : Bool) : Option Registers :=
  let t := testDown ^^ s.cut
  let p := passiveDown ^^ s.cut
  let hit := t && (s.tested == 0)
  if (p && (s.passive == 0)) || (hit && (returnBit ^^ s.cut)) then none
  else some ⟨adjust s.tested t, adjust s.passive p, s.cut ^^ hit⟩

inductive Change where | up | stay | down

def biasPhase (testDown : Bool) (s : Registers) : Option Registers := do
  let s ← command s testDown false false
  let s ← command s testDown true false
  let s ← command s testDown false false
  command s testDown true false

def probe (down : Bool) (s : Registers) : Option Registers := do
  let s ← command s true down false
  command s false (!down) true

def guard (change : Change) (s : Registers) : Option Registers := do
  let first := match change with | .down => true | _ => false
  let second := match change with | .up => false | _ => true
  let s ← biasPhase true s
  let s ← probe first s
  let s ← probe second s
  biasPhase false s

def biased (v : Nat) := 4*v+4

def applyChange (change : Change) (y : Nat) :=
  match change with | .up => y+1 | .stay => y | .down => y-1

private theorem remove_bias (x y : Nat) :
    biasPhase true ⟨x+4,y,false⟩ = some ⟨x,y,false⟩ := rfl

private theorem restore_bias (x y : Nat) :
    biasPhase false ⟨x,y,false⟩ = some ⟨x+4,y,false⟩ := rfl

private theorem probe_pos (x y : Nat) (d : Bool) :
    probe d ⟨x+1,y+1,false⟩ = some ⟨x+1,y+1,false⟩ := by cases d <;> rfl

private theorem probe_zero_up (y : Nat) :
    probe false ⟨0,y,false⟩ = some ⟨0,y+2,false⟩ := rfl

private theorem probe_zero_down (y : Nat) :
    probe true ⟨0,y+2,false⟩ = some ⟨0,y,false⟩ := rfl

theorem guard_correct (change : Change) (x y : Nat)
    (valid : x = 0 → change = .down → y > 0) :
    guard change ⟨biased x, biased y, false⟩ =
      some ⟨biased x, biased (if x = 0 then applyChange change y else y), false⟩ := by
  cases change <;> cases x <;> cases y <;>
    simp_all [guard, biased, applyChange, Nat.mul_succ, Nat.add_assoc, remove_bias,
      restore_bias, probe_pos, probe_zero_up, probe_zero_down, bind, Option.bind] <;> rfl

def Repeats (f : Nat → α) := ∃ i j, i < j ∧ f i = f j
def Covered (f : Nat → α) := ∃ words : List α, ∀ n, f n ∈ words

-- In a repetition-free stream, every finite list has a time after which
-- none of its elements ever appears. Apply this to a proposed finite cover.
private theorem repeats_of_covered {f : Nat → α} (h : Covered f) : Repeats f := by
  classical
  apply Classical.byContradiction
  intro distinct
  have avoid (xs : List α) : ∃ k, ∀ n, k ≤ n → f n ∉ xs := by
    induction xs with
    | nil => exact ⟨0, by simp⟩
    | cons a xs ih =>
      obtain ⟨k, hk⟩ := ih
      by_cases seen : ∃ m, f m = a
      · obtain ⟨m, hm⟩ := seen
        refine ⟨max k (m+1), ?_⟩
        intro n hn
        simp only [List.mem_cons, not_or]
        exact ⟨fun eq => distinct ⟨m, n, by omega, hm.trans eq.symm⟩, hk n (by omega)⟩
      · exact ⟨k, fun n hn hmem => (List.mem_cons.mp hmem).elim
            (fun eq => seen ⟨n, eq⟩) (hk n hn)⟩
  obtain ⟨xs, hall⟩ := h
  obtain ⟨k, hk⟩ := avoid xs
  exact hk k (by omega) (hall k)

private theorem covered_of_repeat {f : Nat → α}
    (det : ∀ i j, f i = f j → f (i+1) = f (j+1)) (h : Repeats f) : Covered f := by
  obtain ⟨i,j,lt,eq⟩ := h
  have shift (d : Nat) : f (i+d) = f (j+d) := by
    induction d with
    | zero => exact eq
    | succ d ih => exact det _ _ ih
  refine ⟨(List.range j).map f, ?_⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < j
    · exact List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩
    · have he := shift (n-j)
      have hj : j+(n-j) = n := by omega
      rw [hj] at he
      rw [← he]
      exact ih _ (by omega)

-- At checkpoint n the bouncing machine occupies a position on the forward
-- source path. false travels forward, true travels backward.
def bounce (stop : Nat → Bool) : Nat → Nat × Bool
  | 0 => (0, false)
  | n+1 =>
    let (k, back) := bounce stop n
    if back then (k-1, k != 0)
    else if stop k then (k, true) else (k+1, false)

private theorem bounce_bounded (stop : Nat → Bool) {h : Nat} (hit : stop h = true)
    (n : Nat) : (bounce stop n).1 ≤ h := by
  induction n with
  | zero => simp [bounce]
  | succ n ih =>
    cases eq : bounce stop n with
    | mk k b =>
      rw [eq] at ih
      change k ≤ h at ih
      simp only [bounce, eq]
      cases b <;> simp
      · split
        · exact ih
        · by_cases e : k = h
          · subst k; simp_all
          · omega
      · omega

private theorem always_forward {stop : Nat → Bool} (live : ∀ i, stop i = false)
    (n : Nat) : bounce stop n = (n,false) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bounce, ih, live]

/-- At the source level the bounce construction itself has an unconditional
halt/repeat equivalence, for every Boolean sequence of halt observations. -/
theorem halt_iff_bounce_repeats (stop : Nat → Bool) :
    (∃ n, stop n = true) ↔ Repeats (bounce stop) := by
  constructor
  · rintro ⟨h, hit⟩
    apply repeats_of_covered
    refine ⟨(List.range (h+1)).flatMap (fun k => [(k,false), (k,true)]), ?_⟩
    intro n
    have bound := bounce_bounded stop hit n
    obtain ⟨k,b,hk⟩ : ∃ k b, bounce stop n = (k,b) := by
      cases e : bounce stop n with | mk k b => exact ⟨k,b,rfl⟩
    rw [hk] at bound ⊢
    exact List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (Nat.lt_succ_of_le bound),
      by cases b <;> simp⟩
  · rintro ⟨i,j,lt,eq⟩
    apply Classical.byContradiction
    intro miss
    have live (n : Nat) : stop n = false := by
      cases e : stop n with
      | false => rfl
      | true => exact False.elim (miss ⟨n,e⟩)
    rw [always_forward live i, always_forward live j] at eq
    have := congrArg Prod.fst eq
    change i = j at this
    omega

-- Successors of distinct live states have distinct values. A fresh entry
-- has no predecessor. Together these exclude a repeated live configuration.
private theorem fresh_path {f : Nat → α} (next : α → Option α)
    (fresh : ∀ x, next x ≠ some (f 0))
    (rev : ∀ x y z, next x = some z → next y = some z → x = y)
    (moves : ∀ n, next (f n) = some (f (n+1))) (i j : Nat) (lt : i < j) :
    f i ≠ f j := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => omega
    | succ j => exact fun eq => fresh _ ((moves j).trans (congrArg some eq.symm))
  | succ i ih =>
    cases j with
    | zero => omega
    | succ j =>
      intro eq
      exact ih j (by omega) (rev _ _ _ ((moves i).trans (congrArg some eq)) (moves j))

/-- The compiler's interface at period boundaries. The physical run takes one
actual tag step per tick. Every source configuration admits a finite list of
possible checkpoint words, and the source configuration can be read back. -/
structure Simulation (source : Nat → α) (stop : Nat → Bool) (queue : Nat → Word) where
  ticks : Nat → Nat
  advancing : ∀ n, ticks n < ticks (n+1)
  physical : ∀ t, step (queue t) = some (queue (t+1))
  decode : Word → α
  readback : ∀ n, decode (queue (ticks n)) = source (bounce stop n).1
  encodings : α → List Word
  bounded : ∀ n, queue (ticks n) ∈ encodings (source (bounce stop n).1)

/-- The final reduction. The source trace may be extended arbitrarily after
halt. Its values up to halt are constrained by the partial transition. -/
theorem halt_iff_queue_repeats {α : Type} (source : Nat → α) (next : α → Option α)
    (halt : α → Bool) (queue : Nat → Word)
    (fresh : ∀ x, next x ≠ some (source 0))
    (rev : ∀ x y z, next x = some z → next y = some z → x = y)
    (moves : ∀ n, halt (source n) = false → next (source n) = some (source (n+1)))
    (sim : Simulation source (fun n => halt (source n)) queue) :
    (∃ n, halt (source n) = true) ↔ Repeats queue := by
  constructor
  · rintro ⟨h, hit⟩
    have cover : Covered (fun n => queue (sim.ticks n)) := by
      refine ⟨(List.range (h+1)).flatMap (fun k => sim.encodings (source k)), ?_⟩
      intro n
      exact List.mem_flatMap.mpr ⟨_, List.mem_range.mpr
        (Nat.lt_succ_of_le (bounce_bounded _ hit n)), sim.bounded n⟩
    obtain ⟨i,j,lt,eq⟩ := repeats_of_covered cover
    have increasing (x y : Nat) (hxy : x < y) : sim.ticks x < sim.ticks y := by
      induction y with
      | zero => omega
      | succ y ih =>
        by_cases e : x = y
        · subst x; exact sim.advancing y
        · exact Nat.lt_trans (ih (by omega)) (sim.advancing y)
    exact ⟨_, _, increasing i j lt, eq⟩
  · intro repeated
    apply Classical.byContradiction
    intro miss
    have live (n : Nat) : halt (source n) = false := by
      cases e : halt (source n) with
      | false => rfl
      | true => exact False.elim (miss ⟨n,e⟩)
    have det (i j : Nat) (eq : queue i = queue j) : queue (i+1) = queue (j+1) :=
      Option.some.inj ((sim.physical i).symm.trans ((congrArg step eq).trans (sim.physical j)))
    obtain ⟨xs, allWords⟩ := covered_of_repeat det repeated
    have cover : Covered source := by
      refine ⟨xs.map sim.decode, ?_⟩
      intro n
      exact List.mem_map.mpr ⟨_, allWords (sim.ticks n), by
        simpa [always_forward live] using sim.readback n⟩
    obtain ⟨i,j,lt,eq⟩ := repeats_of_covered cover
    exact fresh_path next fresh rev (fun n => moves n (live n)) i j lt eq

#print axioms double_block
#print axioms guard_correct
#print axioms halt_iff_bounce_repeats
#print axioms halt_iff_queue_repeats

/-! ## Programmable clocks and cut sweeps -/

-- The lane of the first selected letter after a block.
def pass (p : Bool) : Word → Bool
  | [] => p
  | _ :: xs => pass (!p) xs

theorem pass_append (p : Bool) (u v : Word) :
    pass p (u ++ v) = pass (pass p u) v := by
  induction u generalizing p with
  | nil => rfl
  | cons x xs ih => exact ih (!p)

theorem lane_append (p : Bool) (u v : Word) :
    lane p (u ++ v) = lane p u ++ lane (pass p u) v := by
  induction u generalizing p with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, lane, pass, ih, List.append_assoc]

private theorem pass_D (p s : Bool) : pass p (differentiator s) = (p ^^ s) := by
  cases p <;> cases s <;> rfl

private theorem pass_I (p s : Bool) : pass p (integrator s) = (p ^^ s) := by
  cases p <;> cases s <;> rfl

abbrev Mask := Int → Bool
def delta (m : Mask) : Mask := fun t => m t ^^ m (t-1)
def differences : Nat → Mask → Mask
  | 0, m => m
  | n+1, m => differences n (delta m)

private theorem differences_add (a b : Nat) (m : Mask) :
    differences (a+b) m = differences a (differences b m) := by
  induction b generalizing m with
  | zero => rfl
  | succ b ih => exact ih (delta m)

theorem differences_pow (k : Nat) (m : Mask) (t : Int) :
    differences (2^k) m t = (m t ^^ m (t-(2:Nat)^k)) := by
  induction k generalizing m t with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_two, differences_add, ih, ih, ih]
    push_cast
    have ar : t - (2:Int)^k - (2:Int)^k = t - ((2:Int)^k + (2:Int)^k) := by omega
    rw [ar, Int.pow_succ]
    have twice : (2:Int)^k * 2 = (2:Int)^k + (2:Int)^k := by omega
    rw [twice]
    cases m t <;> cases m (t-(2:Int)^k) <;> cases m (t-((2:Int)^k+(2:Int)^k)) <;> rfl

-- The Boolean list records the differentiator memories, outside to inside.
-- At each layer its integrator remembers that same bit XOR the previous mask.
def clockWord (m : Mask) (t : Int) : List Bool → Word
  | [] => []
  | s :: ss => differentiator s ++ clockWord (delta m) t ss ++ integrator (s ^^ m (t-1))

def clockNext (p : Bool) : List Bool → List Bool
  | [] => []
  | s :: ss => p :: clockNext (p ^^ s) ss

@[simp] theorem clockNext_length (p : Bool) (ss : List Bool) :
    (clockNext p ss).length = ss.length := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih => simp [clockNext, ih]

theorem clock_action (ss : List Bool) (m : Mask)
    (vanish : ∀ t, differences ss.length m t = false) (p : Bool) (t : Int) :
    pass p (clockWord m t ss) = (p ^^ m t) ∧
    lane p (clockWord m t ss) = clockWord m (t+1) (clockNext p ss) := by
  induction ss generalizing m p with
  | nil =>
    have hz : m t = false := vanish t
    simp [clockWord, pass, lane, clockNext, hz]
  | cons s ss ih =>
    have ⟨travel, output⟩ := ih (delta m) vanish (p ^^ s)
    simp only [clockWord, clockNext, pass_append, lane_append, pass_D, pass_I,
      differentiator_lane, integrator_lane, travel, output, Int.add_sub_cancel]
    simp only [delta]
    cases p <;> cases s <;> cases m t <;> cases m (t-1) <;> simp


theorem seeded_clock (k : Nat) (m : Mask) (periodic : ∀ t, m (t-(2:Nat)^k) = m t)
    (ss : List Bool) (size : ss.length = 2^k) (p : Bool) (t : Int) :
    pass p (clockWord m t ss) = (p ^^ m t) ∧
    lane p (clockWord m t ss) = clockWord m (t+1) (clockNext p ss) := by
  apply clock_action
  intro i
  rw [size, differences_pow, periodic]
  simp

def cutWord (cut : Bool) (w : Word) := if cut then w.tail else w

private theorem sweep_pending (xs : Word) (head : Letter) (tail : Word) :
    sweepFrom xs (head :: tail) =
      some (cutWord (pass false xs) ((head :: tail) ++ lane false xs)) := by
  match xs with
  | [] => simp [sweepFrom, pass, lane, cutWord]
  | [x] => simp [sweepFrom, pass, lane, cutWord]
  | x :: y :: rest =>
    simpa [sweepFrom, lane, pass, List.append_assoc] using
      sweep_pending rest head (tail ++ production x)

/-- The protected leading differentiator makes the boundary-crossing deletion
legal, even when a previous sweep has already consumed its first letter. -/
theorem physical_sweep (p s : Bool) (rest : Word) :
    let w := differentiator s ++ rest
    runSteps (sweepSteps (cutWord p w)) (cutWord p w) =
      some (cutWord (pass p w) (lane p w)) := by
  have leading (y : Letter) (xs : Word) :
      runSteps (sweepSteps (D :: y :: xs)) (D :: y :: xs) =
        some (cutWord (pass false xs) (production D ++ lane false xs)) := by
    simpa [sweepFrom] using (sweep_exact (D :: y :: xs) []).trans (sweep_pending xs D [D,e,z])
  cases p <;> cases s <;> apply leading

/-! ## Counter blocks on either lane -/

private theorem copies_add (u : Word) (n m : Nat) :
    tiles u (n+m) = tiles u n ++ tiles u m := by
  induction n with
  | zero => simp [tiles]
  | succ n ih => rw [Nat.succ_add, tiles, ih, tiles, List.append_assoc]

private theorem copies_pass {u : Word} (even : ∀ p, pass p u = p) (n : Nat) (p : Bool) :
    pass p (tiles u n) = p := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tiles, pass_append, even, ih]

private theorem copies_lane {u : Word} (even : ∀ p, pass p u = p) (n : Nat) (p : Bool) :
    lane p (tiles u n) = tiles (lane p u) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tiles, lane_append, even, ih]

private theorem copies_group (u : Word) (n k : Nat) :
    tiles (tiles u k) n = tiles u (n*k) := by
  induction n with
  | zero => simp [tiles]
  | succ n ih => rw [tiles, ih, Nat.succ_mul, Nat.add_comm, copies_add]

inductive DataBlock where
  | units (n : Nat)
  | singles (n : Nat)
  deriving DecidableEq

def DataBlock.word : DataBlock → Word
  | .units n => tiles (production b) n
  | .singles n => tiles [b] n

def DataBlock.next (p : Bool) : DataBlock → DataBlock
  | .units n => .singles (if p then n else n*4)
  | .singles n => .units (n/2 + if n%2 = 1 && !p then 1 else 0)

def DataBlock.exit (p : Bool) : DataBlock → Bool
  | .units _ => p
  | .singles n => p ^^ (n%2 == 1)

private theorem singles_pairs (p : Bool) (n : Nat) :
    lane p (tiles [b] (n*2)) = tiles (production b) n ∧ pass p (tiles [b] (n*2)) = p := by
  rw [← copies_group]
  have even (q : Bool) : pass q (tiles [b] 2) = q := by cases q <;> rfl
  rw [copies_lane even, copies_pass even]
  cases p <;> exact ⟨rfl,rfl⟩

theorem data_action (p : Bool) (v : DataBlock) :
    lane p v.word = (v.next p).word ∧ pass p v.word = v.exit p := by
  cases v with
  | units n =>
    have even (q : Bool) : pass q (production b) = q := by cases q <;> rfl
    simp only [DataBlock.word, DataBlock.next, DataBlock.exit, copies_lane even, copies_pass even,
      and_true]
    cases p
    · exact copies_group [b] n 4
    · rfl
  | singles n =>
    have decomp : n = n/2*2 + n%2 := by omega
    obtain ⟨out, travel⟩ := singles_pairs p (n/2)
    by_cases parity : n%2 = 1
    · have eq : tiles [b] n = tiles [b] (n/2*2) ++ [b] := by
        exact (congrArg (tiles [b]) (show n = n/2*2+1 by omega)).trans (copies_add [b] _ 1)
      simp only [DataBlock.word, DataBlock.next, DataBlock.exit, eq, lane_append, pass_append,
        out, travel, parity]
      cases p <;> simp [lane, pass]
      exact (copies_add (production b) (n/2) 1).symm
    · have eq : tiles [b] n = tiles [b] (n/2*2) := by congr 1; omega
      simp [DataBlock.word, DataBlock.next, DataBlock.exit, eq, out, travel, parity]
      have mod0 : n%2 = 0 := by omega
      simp [mod0]

/-! ## Serializing and advancing a complete layout -/

-- A mask is a finite program table. The signed index also supplies the
-- few pre-time-zero bits needed to initialize a nested clock.
def periodMask (k : Nat) (bits : Fin (2^k) → Bool) : Mask := fun t =>
  bits ⟨(t % ((2:Nat)^k : Nat)).toNat, by
    have hp : 0 < ((2:Nat)^k : Int) := by exact_mod_cast Nat.two_pow_pos k
    have lo := Int.emod_nonneg t (by omega : ((2:Nat)^k : Int) ≠ 0)
    have hi := Int.emod_lt_of_pos t hp
    omega⟩

private theorem periodMask_repeat (k : Nat) (bits : Fin (2^k) → Bool) (t : Int) :
    periodMask k bits (t-((2:Nat)^k : Nat)) = periodMask k bits t := by
  unfold periodMask
  congr 2
  rw [Int.sub_emod]
  simp

structure Clock (k : Nat) where
  bits : Fin (2^k) → Bool
  memory : List Bool
  size : memory.length = 2^k

def Clock.seed (k : Nat) (bits : Fin (2^k) → Bool) : Clock k :=
  ⟨bits, List.replicate (2^k) false, List.length_replicate⟩

inductive Block (k : Nat) where
  | clock (c : Clock k)
  | data (d : DataBlock)

def Block.word (t : Int) : Block k → Word
  | .clock c => clockWord (periodMask k c.bits) t c.memory
  | .data d => d.word

def Block.advance (t : Int) (p : Bool) : Block k → Bool × Block k
  | .clock c => (p ^^ periodMask k c.bits t, .clock ⟨c.bits,clockNext p c.memory,
      (clockNext_length _ _).trans c.size⟩)
  | .data d => (d.exit p,.data (d.next p))

theorem block_action (v : Block k) (t : Int) (p : Bool) :
    pass p (v.word t) = (v.advance t p).1 ∧
    lane p (v.word t) = (v.advance t p).2.word (t+1) := by
  cases v with
  | clock c => exact seeded_clock k _ (by simpa only [Int.natCast_pow, Int.reduceNatCast] using periodMask_repeat k c.bits) _ c.size _ _
  | data d => exact ⟨(data_action p d).2,(data_action p d).1⟩

def layoutWord (t : Int) : List (Block k) → Word
  | [] => []
  | v :: vs => v.word t ++ layoutWord t vs

def advanceLayout (t : Int) (p : Bool) : List (Block k) → Bool × List (Block k)
  | [] => (p, [])
  | v :: vs =>
    let (q, v') := v.advance t p
    let (r, vs') := advanceLayout t q vs
    (r, v' :: vs')

theorem layout_action (vs : List (Block k)) (t : Int) (p : Bool) :
    pass p (layoutWord t vs) = (advanceLayout t p vs).1 ∧
    lane p (layoutWord t vs) = layoutWord (t+1) (advanceLayout t p vs).2 := by
  induction vs generalizing p with
  | nil => exact ⟨rfl,rfl⟩
  | cons v vs ih =>
    have ⟨out, emit⟩ := block_action v t p
    have ⟨out', emit'⟩ := ih (v.advance t p).1
    simp only [layoutWord, advanceLayout, pass_append, lane_append, out, emit, out', emit', and_self]

theorem layout_sweep (c : Clock k) (vs : List (Block k)) (p : Bool) (t : Int) :
    let blocks := Block.clock c :: vs
    let before := cutWord p (layoutWord t blocks)
    let after := advanceLayout t p blocks
    runSteps (sweepSteps before) before = some (cutWord after.1 (layoutWord (t+1) after.2)) := by
  dsimp only
  have ⟨out, emit⟩ := layout_action (.clock c :: vs) t p
  rw [← out, ← emit]
  obtain ⟨bits, memory, size⟩ := c
  cases memory with
  | nil => have := Nat.two_pow_pos k; change 0 = 2^k at size; omega
  | cons s ss =>
    simp only [layoutWord, Block.word, clockWord, List.append_assoc]
    apply physical_sweep

structure Device (k : Nat) where
  head : Clock k
  rest : List (Block k)
  cut : Bool
  time : Int

def Device.blocks (d : Device k) := Block.clock d.head :: d.rest
def Device.word (d : Device k) := cutWord d.cut (layoutWord d.time d.blocks)
def Device.advance (d : Device k) : Device k :=
  let q := d.cut ^^ periodMask k d.head.bits d.time
  let tail := advanceLayout d.time q d.rest
  ⟨⟨d.head.bits, clockNext d.cut d.head.memory, (clockNext_length _ _).trans d.head.size⟩,
    tail.2, tail.1, d.time+1⟩

theorem device_sweep (d : Device k) :
    runSteps (sweepSteps d.word) d.word = some d.advance.word := layout_sweep _ _ _ _

theorem device_progress (d : Device k) : 0 < sweepSteps d.word := by
  obtain ⟨⟨bits,mem,size⟩,rest,p,t⟩ := d
  cases mem with
  | nil => have := Nat.two_pow_pos k; change 0 = 2^k at size; omega
  | cons s ss =>
    cases p <;> cases s <;> apply Nat.add_pos_left (by decide : 0 < 1)

def iterate (f : α → α) (x : α) : Nat → α
  | 0 => x
  | n+1 => f (iterate f x n)

def sweepTicks (d : Device k) : Nat → Nat
  | 0 => 0
  | n+1 => sweepTicks d n + sweepSteps (iterate Device.advance d n).word

theorem runSteps_add (a b : Nat) (w : Word) :
    runSteps (a+b) w = (runSteps a w).bind (runSteps b) := by
  induction a generalizing w with
  | zero => simp [runSteps]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [runSteps]
    cases step w <;> simp [ih]

theorem device_checkpoints (d : Device k) (n : Nat) :
    runSteps (sweepTicks d n) d.word = some (iterate Device.advance d n).word := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sweepTicks, runSteps_add, ih]
    exact device_sweep _

private theorem sweepTicks_ge (d : Device k) (n : Nat) : n ≤ sweepTicks d n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have := device_progress (iterate Device.advance d n)
    simp only [sweepTicks]
    omega

-- Short queues have no successor. All ticks of a compiled device are live.
theorem device_live (d : Device k) (n : Nat) : ∃ w, runSteps n d.word = some w := by
  have h := device_checkpoints d n
  have hle := sweepTicks_ge d n
  generalize eq : sweepTicks d n = m at h hle
  have ar : m = n+(m-n) := by omega
  rw [ar, runSteps_add] at h
  cases hn : runSteps n d.word with
  | none => simp [hn] at h
  | some w => exact ⟨w,rfl⟩

def Device.queue (d : Device k) (t : Nat) := (runSteps t d.word).getD []

theorem device_literal (d : Device k) (n : Nat) :
    step (d.queue n) = some (d.queue (n+1)) := by
  obtain ⟨w, hw⟩ := device_live d n
  obtain ⟨v, hv⟩ := device_live d (n+1)
  have h := hv
  rw [runSteps_add, hw] at h
  cases hs : step w <;> simp_all [Device.queue, runSteps]

theorem device_read_checkpoint (d : Device k) (n : Nat) :
    d.queue (sweepTicks d n) = (iterate Device.advance d n).word := by
  simp [Device.queue, device_checkpoints]

/-! ## Detecting cycles at unbounded checkpoint times -/

def wordsUpTo : Nat → List Word
  | 0 => [[]]
  | n+1 => [] :: [I,D,z,e,a,b].flatMap (fun x => (wordsUpTo n).map (x :: ·))

theorem mem_wordsUpTo {w : Word} (h : w.length ≤ n) : w ∈ wordsUpTo n := by
  induction n generalizing w with
  | zero => cases w <;> simp_all [wordsUpTo]
  | succ n ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons x xs =>
      simp only [wordsUpTo, List.mem_cons, List.mem_flatMap]
      right
      exact ⟨x, by cases x <;> simp, List.mem_map.mpr ⟨xs,ih (by simpa using h),rfl⟩⟩

private theorem member_length_le (ws : List Word) (w : Word) (h : w ∈ ws) :
    w.length ≤ (ws.map List.length).sum := by
  induction ws with
  | nil => simp at h
  | cons v vs ih =>
    obtain eq | elem := List.mem_cons.mp h
    · subst w; simp
    · have := ih elem; simp; omega

theorem repeats_iff_bounded_checkpoints (d : Device k) (times : Nat → Nat)
    (inc : ∀ i j, i < j → times i < times j) :
    Repeats d.queue ↔ ∃ B, ∀ n, (d.queue (times n)).length ≤ B := by
  constructor
  · intro rep
    have det (i j : Nat) (he : d.queue i = d.queue j) : d.queue (i+1) = d.queue (j+1) :=
      Option.some.inj ((device_literal d i).symm.trans ((congrArg step he).trans (device_literal d j)))
    obtain ⟨ws, allW⟩ := covered_of_repeat det rep
    exact ⟨_,fun n => member_length_le ws _ (allW _)⟩
  · rintro ⟨B,hB⟩
    have cover : Covered (fun n => d.queue (times n)) :=
      ⟨wordsUpTo B, fun n => mem_wordsUpTo (hB n)⟩
    obtain ⟨i,j,lt,eq⟩ := repeats_of_covered cover
    exact ⟨_,_,inc i j lt,eq⟩

/-! ## Two-sweep commands on a bank of counters -/

def underflow (e : Nat) (down : Bool) := down && (e == 0)

theorem exponent_pair (e : Nat) (down ret : Bool)
    (readHit : underflow e down = true → ret = false) :
    let start := DataBlock.units (2^e)
    let mid := start.next down
    mid.next ret = DataBlock.units (2^(adjust e down)) ∧
      mid.exit ret = (ret ^^ underflow e down) := by
  cases down with
  | false =>
    simp only [DataBlock.next, DataBlock.exit, Bool.false_eq_true, if_false, underflow,
      Bool.false_and, Bool.bne_false, adjust, Nat.pow_succ]
    have parity : 2^e*4 % 2 = 0 := by omega
    have half : 2^e*4 / 2 = 2^e*2 := by omega
    simp [half, parity]
  | true =>
    cases e with
    | zero =>
      have hr := readHit rfl
      subst ret
      decide
    | succ e =>
      have parity : (2^e*2) % 2 = 0 := by omega
      have half : (2^e*2) / 2 = 2^e := by omega
      simp [DataBlock.next, DataBlock.exit, underflow, adjust, Nat.pow_succ, parity, half]

abbrev Table (k : Nat) := Fin (2^k) → Bool
abbrev Memory (k : Nat) := {s : List Bool // s.length = 2^k}

def maskXor (u v : Table k) : Table k := fun i => u i ^^ v i
def zeroMask (k : Nat) : Table k := fun _ => false

structure Column (k : Nat) where
  mask : Table k
  memory : Memory k
  data : DataBlock

def columns (prev : Table k) (tail : Memory k) : List (Column k) → List (Block k)
  | [] => [.clock ⟨prev,tail.val,tail.property⟩]
  | c :: cs =>
    .clock ⟨maskXor prev c.mask,c.memory.val,c.memory.property⟩ :: .data c.data ::
      columns c.mask tail cs

def nextMemory (p : Bool) (mem : Memory k) : Memory k :=
  ⟨clockNext p mem.val, (clockNext_length _ _).trans mem.property⟩

structure Bank (k : Nat) where
  regs : List (Column k)
  last : Memory k

def Bank.layout (b : Bank k) := columns (zeroMask k) b.last b.regs

def Bank.device (b : Bank k) (cut : Bool) (t : Int) : Device k :=
  match b.regs with
  | [] => ⟨⟨zeroMask k,b.last.val,b.last.property⟩,[],cut,t⟩
  | c :: cs => ⟨⟨maskXor (zeroMask k) c.mask,c.memory.val,c.memory.property⟩,
                  .data c.data :: columns c.mask b.last cs,cut,t⟩

theorem bank_layout (b : Bank k) (p : Bool) (t : Int) :
    (b.device p t).blocks = b.layout := by cases b with | mk cs tail => cases cs <;> rfl

-- p is the running boundary cut, before XORing in the current mask.
def walk (t : Int) (tail : Memory k) (p : Bool) (prev : Table k) :
    List (Column k) → Bool × Bank k
  | [] => (p,⟨[],nextMemory (p ^^ periodMask k prev t) tail⟩)
  | c :: cs =>
    let q := p ^^ periodMask k c.mask t
    let p' := c.data.exit q ^^ periodMask k c.mask t
    let (lastCut, rest) := walk t tail p' c.mask cs
    (lastCut,⟨⟨c.mask,nextMemory (p ^^ periodMask k prev t) c.memory,c.data.next q⟩ ::
      rest.regs,rest.last⟩)

private theorem xor_cancel_left (p x y : Bool) : ((p ^^ x) ^^ (x ^^ y)) = (p ^^ y) := by
  cases p <;> cases x <;> cases y <;> rfl

private theorem xor_cancel_twice (p x : Bool) : ((p ^^ x) ^^ x) = p := by
  cases p <;> cases x <;> rfl

theorem walk_layout (t : Int) (tail : Memory k) (p : Bool) (prev : Table k)
    (cs : List (Column k)) :
    advanceLayout t (p ^^ periodMask k prev t) (columns prev tail cs) =
      ((walk t tail p prev cs).1, columns prev (walk t tail p prev cs).2.last
        (walk t tail p prev cs).2.regs) := by
  induction cs generalizing p prev with
  | nil =>
    simp [walk, columns, advanceLayout, Block.advance, nextMemory, xor_cancel_twice]
  | cons c cs ih =>
    simp only [walk, columns, advanceLayout, Block.advance]
    have maskEq : periodMask k (maskXor prev c.mask) t =
        (periodMask k prev t ^^ periodMask k c.mask t) := rfl
    simp only [maskEq, xor_cancel_left]
    have h := ih ((c.data.exit (p ^^ periodMask k c.mask t)) ^^ periodMask k c.mask t) c.mask
    rw [xor_cancel_twice] at h
    rw [h]
    rfl

def Bank.advance (b : Bank k) (p : Bool) (t : Int) := walk t b.last p (zeroMask k) b.regs

private theorem device_ext {u v : Device k} (blocks : u.blocks = v.blocks)
    (cut : u.cut = v.cut) (time : u.time = v.time) : u = v := by
  cases u; cases v
  simp_all [Device.blocks]

theorem bank_sweep (b : Bank k) (p : Bool) (t : Int) :
    (b.device p t).advance = (b.advance p t).2.device (b.advance p t).1 (t+1) := by
  have h := walk_layout t b.last p (zeroMask k) b.regs
  have hz : periodMask k (zeroMask k) t = false := rfl
  simp only [hz, Bool.bne_false] at h
  have hab (d : Device k) : (d.advance.cut, d.advance.blocks) =
      advanceLayout d.time d.cut d.blocks := rfl
  have ht (x : Bank k) (q : Bool) (a : Int) : (x.device q a).time = a := by
    cases x with | mk cs tail => cases cs <;> rfl
  have hc (x : Bank k) (q : Bool) (a : Int) : (x.device q a).cut = q := by
    cases x with | mk cs tail => cases cs <;> rfl
  have h' := hab (b.device p t)
  rw [bank_layout, ht, hc] at h'
  have both := h'.trans h
  apply device_ext
  · rw [bank_layout]; exact congrArg Prod.snd both
  · rw [hc]; exact congrArg Prod.fst both
  · rw [ht]; change (b.device p t).time + 1 = t+1; rw [ht]

abbrev View (k : Nat) := List (Table k × DataBlock)
def view (cs : List (Column k)) : View k := cs.map (fun c => (c.mask,c.data))

def sweepView (t : Int) (p : Bool) : View k → Bool × View k
  | [] => (p,[])
  | (m,d) :: cs =>
    let q := p ^^ periodMask k m t
    let (r,rest) := sweepView t (d.exit q ^^ periodMask k m t) cs
    (r,(m,d.next q) :: rest)

theorem walk_view (t : Int) (tail : Memory k) (p : Bool) (prev : Table k) (cs : List (Column k)) :
    ((walk t tail p prev cs).1,view (walk t tail p prev cs).2.regs) = sweepView t p (view cs) := by
  induction cs generalizing p prev with
  | nil => rfl
  | cons c cs ih =>
    simp only [walk, view, List.map_cons, sweepView]
    have h := ih (c.data.exit (p ^^ periodMask k c.mask t) ^^ periodMask k c.mask t) c.mask
    exact congrArg (fun res : Bool × View k => (res.1,(c.mask,c.data.next (p ^^ periodMask k c.mask t)) :: res.2)) h

abbrev Exponents (k : Nat) := List (Table k × Nat)
def unitsView (xs : Exponents k) : View k :=
  xs.map (fun (m,exp) => (m,DataBlock.units (2^exp)))

def middleView (t : Int) (p : Bool) (xs : Exponents k) : View k :=
  xs.map (fun (m,exp) => (m,(DataBlock.units (2^exp)).next (p ^^ periodMask k m t)))

theorem first_sweep (t : Int) (p : Bool) (xs : Exponents k) :
    sweepView t p (unitsView xs) = (p,middleView t p xs) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨m,exp⟩ := c
    simp only [unitsView, List.map_cons, sweepView, DataBlock.exit, xor_cancel_twice] at ih ⊢
    rw [ih]
    rfl

-- An exact command interpreter. Failure indicates a singleton entered on
-- lane one. Its first lane is shared across all registers; its return lane
-- accumulates the parity changes of earlier singleton blocks.
def evalPair (t : Int) (start returnCut : Bool) : Exponents k → Option (Bool × Exponents k)
  | [] => some (returnCut,[])
  | (m,exp) :: cs => do
    let down := start ^^ periodMask k m t
    let ret := returnCut ^^ periodMask k m (t+1)
    let hit := underflow exp down
    if hit && ret then none else
      let (q,rest) ← evalPair t start (returnCut ^^ hit) cs
      return (q,(m,adjust exp down) :: rest)

theorem second_sweep (t : Int) (start ret q : Bool) (xs ys : Exponents k)
    (h : evalPair t start ret xs = some (q,ys)) :
    sweepView (t+1) ret (middleView t start xs) = (q,unitsView ys) := by
  induction xs generalizing ret q ys with
  | nil =>
    simp [evalPair] at h
    obtain ⟨rfl,rfl⟩ := h
    rfl
  | cons c cs ih =>
    obtain ⟨m,exp⟩ := c
    let down := start ^^ periodMask k m t
    let lane2 := ret ^^ periodMask k m (t+1)
    let hit := underflow exp down
    change (if hit && lane2 then none else
      (evalPair t start (ret ^^ hit) cs).bind (fun (lastCut,rest) => some (lastCut,(m,adjust exp down)::rest))) = _ at h
    split at h
    · contradiction
    · rename_i ok
      have good : hit = true → lane2 = false := by simpa using ok
      obtain ⟨a,b⟩ := exponent_pair exp down lane2 good
      cases he : evalPair t start (ret ^^ hit) cs with
      | none => simp [he] at h
      | some result =>
        obtain ⟨r,rest⟩ := result
        simp [he] at h
        obtain ⟨rfl,rfl⟩ := h
        have tail := ih _ _ _ he
        have exitEq : (((DataBlock.units (2^exp)).next down).exit lane2 ^^ periodMask k m (t+1)) =
            (ret ^^ hit) := by rw [b]; unfold lane2 hit; cases ret <;> cases periodMask k m (t+1) <;> cases underflow exp down <;> rfl
        change ((sweepView (t+1) _ (middleView t start cs)).1,
          (m,((DataBlock.units (2^exp)).next down).next lane2) ::
          (sweepView (t+1) _ (middleView t start cs)).2) = _
        rw [exitEq,tail,a]
        rfl

theorem bank_command (b : Bank k) (p q : Bool) (t : Int) (xs ys : Exponents k)
    (initial : view b.regs = unitsView xs)
    (ok : evalPair t p p xs = some (q,ys)) :
    ∃ b' : Bank k, ((b.device p t).advance).advance = b'.device q (t+2) ∧
      view b'.regs = unitsView ys := by
  let mid := b.advance p t
  have h1 : (mid.1,view mid.2.regs) = (p,middleView t p xs) :=
    (walk_view t b.last p _ b.regs).trans (initial ▸ first_sweep t p xs)
  have cut1 := congrArg Prod.fst h1
  have view1 := congrArg Prod.snd h1
  let final := mid.2.advance p (t+1)
  have h2 : (final.1,view final.2.regs) = (q,unitsView ys) := by
    have h := walk_view (t+1) mid.2.last p (zeroMask k) mid.2.regs
    change view mid.2.regs = middleView t p xs at view1
    rw [view1, second_sweep _ _ _ _ _ _ ok] at h
    exact h
  refine ⟨final.2, ?_, congrArg Prod.snd h2⟩
  rw [bank_sweep]
  change (mid.2.device mid.1 (t+1)).advance = _
  change mid.1 = p at cut1
  rw [cut1,bank_sweep]
  rw [show t+1+1 = t+2 by omega]
  change final.2.device final.1 (t+2) = _
  rw [show final.1 = q from congrArg Prod.fst h2]

def seedBank (k : Nat) (xs : Exponents k) : Bank k :=
  let mem : Memory k := ⟨List.replicate (2^k) false,List.length_replicate⟩
  ⟨xs.map (fun (m,n) => ⟨m,mem,.units (2^n)⟩),mem⟩

theorem seed_view (xs : Exponents k) : view (seedBank k xs).regs = unitsView xs := by
  simp [view, seedBank, unitsView, List.map_map, Function.comp_def]

theorem iterate_add (f : α → α) (x : α) (m n : Nat) :
    iterate f x (m+n) = iterate f (iterate f x m) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f ih

-- A sequence of successful abstract commands is realized by one uninterrupted
-- trajectory from the seed. Clocks and their cut bits are carried across steps.
theorem commands_realized (xs : Nat → Exponents k) (cut : Nat → Bool)
    (commands : ∀ n : Nat, evalPair (2*n) (cut n) (cut n) (xs n) = some (cut (n+1),xs (n+1)))
    (n : Nat) :
    ∃ b : Bank k, iterate Device.advance ((seedBank k (xs 0)).device (cut 0) 0) (2*n) =
      b.device (cut n) (2*n) ∧ view b.regs = unitsView (xs n) := by
  induction n with
  | zero => exact ⟨_,rfl,seed_view _⟩
  | succ n ih =>
    obtain ⟨b,hd,hv⟩ := ih
    obtain ⟨b',h',v'⟩ := bank_command b _ _ _ _ _ hv (commands n)
    refine ⟨b',?_,v'⟩
    rw [Nat.mul_succ,iterate_add,hd]
    change ((b.device (cut n) (2*n)).advance).advance = b'.device (cut (n+1)) _
    rw [h']
    congr 1 <;> omega

private theorem clock_length (ss : List Bool) (m : Mask) (t : Int) :
    (clockWord m t ss).length ≤ 10 * ss.length := by
  induction ss generalizing m with
  | nil => simp [clockWord]
  | cons s ss ih =>
    have hi (x : Bool) : (integrator x).length ≤ 5 := by cases x <;> decide
    have hd (x : Bool) : (differentiator x).length ≤ 5 := by cases x <;> decide
    simp only [clockWord, List.length_append, List.length_cons, Nat.mul_succ]
    have := ih (delta m)
    have := hi (s ^^ m (t-1))
    have := hd s
    omega

def dataSize (vs : List (Block k)) : Nat :=
  (vs.map (fun | .clock _ => 0 | .data d => d.word.length)).sum

theorem layout_length (vs : List (Block k)) (t : Int) :
    dataSize vs ≤ (layoutWord t vs).length ∧
    (layoutWord t vs).length ≤ dataSize vs + vs.length*(10*2^k) := by
  induction vs with
  | nil => simp [dataSize,layoutWord]
  | cons v vs ih =>
    cases v with
    | clock c =>
      have h := clock_length c.memory (periodMask k c.bits) t
      rw [c.size] at h
      simp only [layoutWord, Block.word, List.length_append, dataSize, List.map_cons,
        List.sum_cons, Nat.zero_add, List.length_cons] at *
      rw [Nat.succ_mul]
      omega
    | data val =>
      simp only [layoutWord, Block.word, List.length_append, dataSize, List.map_cons,
        List.sum_cons, List.length_cons] at *
      rw [Nat.succ_mul]
      omega

@[simp] theorem layout_count (vs : List (Block k)) (t : Int) (p : Bool) :
    (advanceLayout t p vs).2.length = vs.length := by
  induction vs generalizing p with
  | nil => rfl
  | cons v vs ih => simp [advanceLayout,ih]

private theorem device_count (d : Device k) (n : Nat) :
    (iterate Device.advance d n).blocks.length = d.blocks.length := by
  induction n with
  | zero => rfl
  | succ n ih => exact (layout_count _ _ _).trans ih

private theorem cut_length (w : Word) (p : Bool) :
    (cutWord p w).length ≤ w.length ∧ w.length ≤ (cutWord p w).length+1 := by
  cases p <;> cases w <;> simp [cutWord]

private theorem ticks_strict (d : Device k) (i j : Nat) (h : i < j) :
    sweepTicks d i < sweepTicks d j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have := device_progress (iterate Device.advance d j)
    simp only [sweepTicks]
    by_cases i = j
    · subst i; omega
    · have := ih (by omega); omega

theorem queue_repeats_iff_bounded_data (d : Device k) (sweeps : Nat → Nat)
    (inc : ∀ i j, i < j → sweeps i < sweeps j) :
    Repeats d.queue ↔ ∃ bound, ∀ n,
      dataSize (iterate Device.advance d (sweeps n)).blocks ≤ bound := by
  rw [repeats_iff_bounded_checkpoints d (fun n => sweepTicks d (sweeps n))
    (fun i j h => ticks_strict d _ _ (inc i j h))]
  constructor
  · rintro ⟨B,h⟩
    refine ⟨B+1,fun n => ?_⟩
    have hb := h n
    rw [device_read_checkpoint] at hb
    let cur := iterate Device.advance d (sweeps n)
    have h₁ := (layout_length cur.blocks cur.time).1
    have h₂ := (cut_length (layoutWord cur.time cur.blocks) cur.cut).2
    change cur.word.length ≤ B at hb
    change (layoutWord cur.time cur.blocks).length ≤ cur.word.length+1 at h₂
    exact Nat.le_trans h₁ (Nat.le_trans h₂ (by omega))
  · rintro ⟨B,h⟩
    refine ⟨B+d.blocks.length*(10*2^k),fun n => ?_⟩
    rw [device_read_checkpoint]
    let cur := iterate Device.advance d (sweeps n)
    have hc : cur.blocks.length = d.blocks.length := device_count d _
    have h₁ := (layout_length cur.blocks cur.time).2
    have h₂ := (cut_length (layoutWord cur.time cur.blocks) cur.cut).1
    rw [hc] at h₁
    exact Nat.le_trans h₂ (Nat.le_trans h₁ (Nat.add_le_add_right (h n) _))

/-! ## Compiling a guarded logical update -/

structure Micro where
  testDown : Bool
  passiveDown : Change → Bool
  returnBit : Bool

def signOf (s : Bool) : Change → Bool := fun _ => s

def guardRows : List Micro :=
  let bias (s : Bool) : List Micro := [⟨s,signOf false,false⟩,⟨s,signOf true,false⟩,
    ⟨s,signOf false,false⟩,⟨s,signOf true,false⟩]
  let pair (f : Change → Bool) : List Micro := [⟨true,f,false⟩,⟨false,fun c => !(f c),true⟩]
  bias true ++ pair (fun | .down => true | _ => false) ++
    pair (fun | .up => false | _ => true) ++ bias false

def microRun (ch : Change) : List Micro → Registers → Option Registers
  | [], s => some s
  | op :: ops, s => (command s op.testDown (op.passiveDown ch) op.returnBit).bind (microRun ch ops)

theorem micro_guard (ch : Change) (s : Registers) : microRun ch guardRows s = guard ch s := by
  simp only [guardRows, List.cons_append, List.nil_append, microRun, guard, biasPhase, probe,
    signOf, bind, Option.bind_assoc, pure, Option.bind_some]

structure Gate (ι : Type) where
  test : ι
  changes : ι → Change

abbrev File (ι : Type) := ι → Nat

def rowExps (masks : ι → Table k) (file : File ι) (order : List ι) : Exponents k :=
  order.map (fun i => (masks i,file i))

def Gate.sign [DecidableEq ι] (g : Gate ι) (op : Micro) (i : ι) :=
  if i = g.test then op.testDown else op.passiveDown (g.changes i)

def Gate.ret [DecidableEq ι] (g : Gate ι) (op : Micro) (i : ι) :=
  if i = g.test then op.returnBit else false

private theorem eval_passives (t : Int) (p ret : Bool) (order : List ι) (xs zs : File ι)
    (masks : ι → Table k)
    (safe : ∀ i ∈ order, underflow (xs i) (p ^^ periodMask k (masks i) t) = false)
    (value : ∀ i ∈ order, adjust (xs i) (p ^^ periodMask k (masks i) t) = zs i)
    (tail tail' : Exponents k) (q : Bool) (endRun : evalPair t p ret tail = some (q,tail')) :
    evalPair t p ret (rowExps masks xs order ++ tail) = some (q,rowExps masks zs order ++ tail') := by
  induction order with
  | nil => exact endRun
  | cons i indices ih =>
    have tailRun := ih (fun j hj => safe j (List.mem_cons_of_mem _ hj))
      (fun j hj => value j (List.mem_cons_of_mem _ hj))
    have hs := safe i (by simp)
    have hv := value i (by simp)
    simp only [rowExps,List.map_cons,List.cons_append,evalPair,hs,hv,Bool.false_and,
      Bool.false_eq_true,if_false,Bool.bne_false]
    change evalPair t p ret (rowExps masks xs indices ++ tail) = _ at tailRun
    simp [rowExps] at tailRun
    simp [tailRun]

-- The distinguished test occurs once in the physical order. The ghost passive
-- value at the test position is ignored when assembling the exponent file.
structure Placement (order : List ι) (test : ι) where
  before : List ι
  after : List ι
  split : order = before ++ test :: after
  earlier : test ∉ before
  later : test ∉ after

private theorem eval_one_test [DecidableEq ι] (order : List ι) (g : Gate ι)
    (place : Placement order g.test) (op : Micro) (t : Int) (p q : Bool)
    (masks : ι → Table k) (sign : ∀ i, periodMask k (masks i) t = g.sign op i)
    (ret : ∀ i, periodMask k (masks i) (t+1) = g.ret op i)
    (xs zs : File ι) (testNew : zs g.test = adjust (xs g.test) (p ^^ op.testDown))
    (cutNew : q = (p ^^ underflow (xs g.test) (p ^^ op.testDown)))
    (hitRead : underflow (xs g.test) (p ^^ op.testDown) = true → (p ^^ op.returnBit) = false)
    (safe : ∀ i, i ≠ g.test → underflow (xs i) (p ^^ op.passiveDown (g.changes i)) = false)
    (value : ∀ i, i ≠ g.test → zs i = adjust (xs i) (p ^^ op.passiveDown (g.changes i))) :
    evalPair t p p (rowExps masks xs order) = some (q,rowExps masks zs order) := by
  have hs (i : ι) (ne : i ≠ g.test) : underflow (xs i) (p ^^ periodMask k (masks i) t) = false := by
    simpa [sign,Gate.sign,ne] using safe i ne
  have hv (i : ι) (ne : i ≠ g.test) : adjust (xs i) (p ^^ periodMask k (masks i) t) = zs i := by
    simpa [sign,Gate.sign,ne] using (value i ne).symm
  have post := eval_passives t p q place.after xs zs masks
    (fun i hi => hs i (fun eq => place.later (eq ▸ hi)))
    (fun i hi => hv i (fun eq => place.later (eq ▸ hi))) [] [] q rfl
  simp only [List.append_nil] at post
  rw [place.split]
  simp only [rowExps,List.map_append,List.map_cons]
  apply eval_passives
  · intro i hi; apply hs; intro eq; exact place.earlier (eq ▸ hi)
  · intro i hi; apply hv; intro eq; exact place.earlier (eq ▸ hi)
  · have skip : (underflow (xs g.test) (p ^^ op.testDown) && (p ^^ op.returnBit)) = false := by
      cases h : underflow (xs g.test) (p ^^ op.testDown) <;> simp_all
    change (if underflow (xs g.test) (p ^^ periodMask k (masks g.test) t) &&
          (p ^^ periodMask k (masks g.test) (t+1)) then none else
        (evalPair t p (p ^^ underflow (xs g.test) (p ^^ periodMask k (masks g.test) t))
          (rowExps masks xs place.after)).bind (fun (v : Bool × Exponents k) =>
          some (v.1,(masks g.test,adjust (xs g.test) (p ^^ periodMask k (masks g.test) t))::v.2))) = _
    have sg : periodMask k (masks g.test) t = op.testDown := by simp [sign,Gate.sign]
    have rt : periodMask k (masks g.test) (t+1) = op.returnBit := by simp [ret,Gate.ret]
    rw [sg,rt,skip,if_neg (by decide),← cutNew,← testNew,post]
    rfl

def agrees [DecidableEq ι] (masks : ι → Table k) (g : Gate ι) (t : Int) : List Micro → Prop
  | [] => True
  | op :: ops => (∀ i, periodMask k (masks i) t = g.sign op i) ∧
      (∀ i, periodMask k (masks i) (t+1) = g.ret op i) ∧ agrees masks g (t+2) ops

def joined [DecidableEq ι] (g : Gate ι) (x : Nat) (ys : File ι) (i : ι) :=
  if i = g.test then x else ys i

private theorem micro_realized [DecidableEq ι] (order : List ι) (g : Gate ι)
    (place : Placement order g.test) (masks : ι → Table k) (ops : List Micro) (t : Int)
    (matchRows : agrees masks g t ops) (x x' : Nat) (ys ys' : File ι) (p q : Bool)
    (success : ∀ i, microRun (g.changes i) ops ⟨x,ys i,p⟩ = some ⟨x',ys' i,q⟩)
    (b : Bank k) (initial : view b.regs = unitsView (rowExps masks (joined g x ys) order)) :
    ∃ b' : Bank k, iterate Device.advance (b.device p t) (2*ops.length) =
       b'.device q (t+2*(ops.length: Int)) ∧
       view b'.regs = unitsView (rowExps masks (joined g x' ys') order) := by
  induction ops generalizing t x ys p b with
  | nil =>
    have eqs (i : ι) : x = x' ∧ ys i = ys' i ∧ p = q := by simpa [microRun] using success i
    obtain ⟨rfl,_,rfl⟩ := eqs g.test
    have eqy : ys = ys' := funext (fun i => (eqs i).2.1)
    subst ys'
    exact ⟨b,by simp [iterate],initial⟩
  | cons op ops ih =>
    let down := op.testDown ^^ p
    let hit := underflow x down
    let nx := adjust x down
    let np := p ^^ hit
    let ny (i : ι) := adjust (ys i) (op.passiveDown (g.changes i) ^^ p)
    have info (i : ι) : underflow (ys i) (op.passiveDown (g.changes i) ^^ p) = false ∧
        (hit = true → (op.returnBit ^^ p) = false) ∧
        microRun (g.changes i) ops ⟨nx,ny i,np⟩ = some ⟨x',ys' i,q⟩ := by
      have h := success i
      simp only [microRun,command] at h
      split at h
      · contradiction
      · rename_i noFail
        change ¬(_ || _) = true at noFail
        simp only [Bool.or_eq_true, not_or, Bool.and_eq_true, Bool.not_eq_true] at noFail
        exact ⟨by simpa [underflow] using noFail.1,fun he => by
          have yes : (op.testDown ^^ p) = true ∧ (x == 0) = true := by
            simpa [hit,underflow,down] using he
          cases eq : op.returnBit ^^ p
          · rfl
          · exact False.elim (noFail.2 ⟨yes,eq⟩), h⟩
    obtain ⟨sg,rt,nextMatch⟩ := matchRows
    have ok := eval_one_test order g place op t p np masks sg rt
      (joined g x ys) (joined g nx ny)
      (by simp [joined,nx,down,Bool.xor_comm])
      (by simp [joined,np,hit,down,Bool.xor_comm])
      (by simpa [joined,hit,down,Bool.xor_comm] using (info g.test).2.1)
      (fun i ne => by simpa [joined,ne,Bool.xor_comm] using (info i).1)
      (fun i ne => by simp [joined,ne,ny,Bool.xor_comm])
    obtain ⟨mid,stepEq,viewEq⟩ := bank_command b _ _ _ _ _ initial ok
    obtain ⟨last,lastEq,lastView⟩ := ih (t+2) nextMatch nx ny np (fun i => (info i).2.2) mid viewEq
    refine ⟨last,?_,lastView⟩
    rw [show 2*(op::ops).length = 2+2*ops.length by simp [Nat.mul_succ,Nat.add_comm],
      iterate_add]
    change iterate Device.advance ((b.device p t).advance.advance) _ = _
    rw [stepEq,lastEq]
    congr 1 <;> simp <;> omega

def Gate.update [DecidableEq ι] (g : Gate ι) (xs : File ι) (i : ι) :=
  if i = g.test then xs i else if xs g.test = 0 then applyChange (g.changes i) (xs i) else xs i

def Gate.valid (g : Gate ι) (xs : File ι) := ∀ i, xs g.test = 0 → g.changes i = .down → xs i > 0

theorem gate_realized [DecidableEq ι] (order : List ι) (g : Gate ι) (place : Placement order g.test)
    (masks : ι → Table k) (t : Int) (schedule : agrees masks g t guardRows)
    (xs : File ι) (valid : g.valid xs) (b : Bank k)
    (initial : view b.regs = unitsView (rowExps masks (biased ∘ xs) order)) :
    ∃ b' : Bank k, iterate Device.advance (b.device false t) 24 = b'.device false (t+24) ∧
      view b'.regs = unitsView (rowExps masks (biased ∘ g.update xs) order) := by
  let x := xs g.test
  let ys' i := biased (if x = 0 then applyChange (g.changes i) (xs i) else xs i)
  have h (i : ι) := (micro_guard (g.changes i) ⟨biased x,biased (xs i),false⟩).trans
    (guard_correct (g.changes i) x (xs i) (valid i))
  have ji : joined g (biased x) (biased ∘ xs) = biased ∘ xs := by
    funext i; by_cases eq : i = g.test <;> simp [eq,joined,x,Function.comp_def]
  have jo : joined g (biased x) ys' = biased ∘ g.update xs := by
    funext i; by_cases eq : i = g.test <;> simp [eq,joined,x,ys',Gate.update,Function.comp_def]
  obtain ⟨b',he,hv⟩ := micro_realized order g place masks guardRows t schedule (biased x) (biased x)
    (biased ∘ xs) ys' false false h b (by rw [ji]; exact initial)
  exact ⟨b',he,jo ▸ hv⟩

abbrev Frames (ι : Type) := List (ι → Bool)
def microFrames [DecidableEq ι] (g : Gate ι) : List Micro → Frames ι
  | [] => []
  | op :: ops => g.sign op :: g.ret op :: microFrames g ops

def Matches (masks : ι → Table k) (t : Int) : Frames ι → Prop
  | [] => True
  | f :: fs => (∀ i, periodMask k (masks i) t = f i) ∧ Matches masks (t+1) fs

private theorem matches_append (u v : Frames ι) (t : Int) (m : ι → Table k) :
    Matches m t (u++v) ↔ Matches m t u ∧ Matches m (t+u.length) v := by
  induction u generalizing t with
  | nil => simp [Matches]
  | cons f fs ih =>
    simp only [List.cons_append, Matches, ih, List.length_cons, Int.natCast_succ]
    rw [show t+1+(fs.length:Int) = t+(fs.length+1) by omega, and_assoc]

private theorem matches_micro [DecidableEq ι] (g : Gate ι) (ops : List Micro) (t : Int)
    (m : ι → Table k) (ok : Matches m t (microFrames g ops)) : agrees m g t ops := by
  induction ops generalizing t with
  | nil => trivial
  | cons op ops ih =>
    obtain ⟨h₁,h₂,tail⟩ := ok
    exact ⟨h₁,h₂,ih _ (by simpa only [show t+2=t+1+1 by omega] using tail)⟩

def tableOf (frames : Frames ι) (i : ι) : Table k :=
  fun j => (frames[j.val]?.getD (fun _ => false)) i

private theorem matches_of_lookup (frames : Frames ι) (masks : ι → Table k) (t : Int)
    (ok : ∀ (j : Fin frames.length) i, periodMask k (masks i) (t+j.val) = frames[j.val] i) :
    Matches masks t frames := by
  induction frames generalizing t with
  | nil => trivial
  | cons f fs ih =>
    constructor
    · intro i; simpa using ok ⟨0,by simp⟩ i
    · apply ih
      intro j i
      have h := ok ⟨j.val+1,by simp [j.isLt]⟩ i
      simpa [Int.natCast_succ,Int.add_assoc,Int.add_comm 1] using h

theorem table_matches (frames : Frames ι) (size : frames.length = 2^k) (lap : Nat) :
    Matches (tableOf (k:=k) frames) ((lap*(2^k):Nat):Int) frames := by
  apply matches_of_lookup
  intro j i
  have pos : 0 < (2^k:Nat) := Nat.two_pow_pos k
  have lt : j.val < 2^k := size ▸ j.isLt
  have within : 0 ≤ (j.val:Int) := by omega
  have limit : (j.val:Int) < ((2^k:Nat):Int) := by exact_mod_cast lt
  have mod : (((lap*(2^k):Nat):Int)+j.val) % ((2^k:Nat):Int) = j.val := by
    rw [Int.natCast_mul,Int.add_emod]; simp [Int.emod_eq_of_lt within limit]
  unfold periodMask tableOf
  change frames[((((lap*(2^k):Nat):Int)+j.val) % ((2^k:Nat):Int)).toNat]?.getD (fun _ => false) i = _
  rw [mod]; simp [j.isLt]

def idleFrames (ι : Type) : Frames ι :=
  [fun _ => false,fun _ => false,fun _ => true,fun _ => false]

private theorem uniform_eval (order : List ι) (m : ι → Table k) (t : Int) (xs : File ι)
    (sg : Bool) (sign : ∀ i, periodMask k (m i) t = sg)
    (safe : ∀ i, underflow (xs i) sg = false) :
    evalPair t false false (rowExps m xs order) =
      some (false,rowExps m (fun i => adjust (xs i) sg) order) := by
  have h := eval_passives t false false order xs (fun i => adjust (xs i) sg) m
    (fun i _ => by simpa [sign] using safe i) (fun i _ => by simp [sign]) [] [] false rfl
  simpa using h

theorem idle_realized (order : List ι) (m : ι → Table k) (t : Int)
    (schedule : Matches m t (idleFrames ι)) (xs : File ι) (b : Bank k)
    (initial : view b.regs = unitsView (rowExps m xs order)) :
    ∃ last : Bank k, iterate Device.advance (b.device false t) 4 = last.device false (t+4) ∧
      view last.regs = unitsView (rowExps m xs order) := by
  obtain ⟨inc,_,dec,_,_⟩ := schedule
  have h := uniform_eval order m t xs false inc (fun _ => rfl)
  obtain ⟨mid,first,hv⟩ := bank_command b false false t _ _ initial h
  have h' := uniform_eval order m (t+2) (fun i => adjust (xs i) false) true
    (by simpa only [show t+2=t+1+1 by omega] using dec) (fun i => by simp [adjust,underflow])
  obtain ⟨last,second,lastV⟩ := bank_command mid false false (t+2) _ _ hv h'
  refine ⟨last, ?_, ?_⟩
  · change ((b.device false t).advance.advance).advance.advance = _
    rw [first,second,show t+2+2=t+4 by omega]
  · exact lastV

/-! ## Assembling and padding a periodic program -/

abbrev Code (ι : Type) := List (Option (Gate ι))
def framesOf [DecidableEq ι] : Code ι → Frames ι
  | [] => []
  | none :: rest => idleFrames ι ++ framesOf rest
  | some g :: rest => microFrames g guardRows ++ framesOf rest

inductive Executes [DecidableEq ι] : Code ι → File ι → File ι → Prop
  | nil (x) : Executes [] x x
  | idle : Executes rest x y → Executes (none :: rest) x y
  | gate (h : g.valid x) : Executes rest (g.update x) y → Executes (some g :: rest) x y

private theorem frames_realized [DecidableEq ι] (order : List ι)
    (place : ∀ i, Placement order i) (code : Code ι) (xs ys : File ι)
    (exec : Executes code xs ys) (m : ι → Table k) (b : Bank k) (t : Int)
    (schedule : Matches m t (framesOf code))
    (initial : view b.regs = unitsView (rowExps m (biased ∘ xs) order)) :
    ∃ last : Bank k, iterate Device.advance (b.device false t) (framesOf code).length =
       last.device false (t+((framesOf code).length:Int)) ∧
       view last.regs = unitsView (rowExps m (biased ∘ ys) order) := by
  induction exec generalizing t b with
  | nil => exact ⟨b,by simp [framesOf,iterate],initial⟩
  | @idle rest x y _ ih =>
    obtain ⟨h₁,h₂⟩ := (matches_append _ _ _ _).mp schedule
    obtain ⟨mid,eq,hv⟩ := idle_realized order m t h₁ (biased ∘ x) b initial
    obtain ⟨last,finish,lastV⟩ := ih mid (t+4) h₂ hv
    refine ⟨last,?_,lastV⟩
    simp only [framesOf,List.length_append,iterate_add]
    change iterate _ (iterate _ _ 4) _ = _
    rw [eq,finish]; congr 1; push_cast; change t+4+_ = t+(4+_); omega
  | @gate rest y g x valid _ ih =>
    obtain ⟨h₁,h₂⟩ := (matches_append _ _ _ _).mp schedule
    obtain ⟨mid,eq,hv⟩ := gate_realized order g (place _) m t
      (matches_micro g guardRows t m h₁) x valid b initial
    obtain ⟨last,finish,lastV⟩ := ih mid (t+24) h₂ hv
    refine ⟨last,?_,lastV⟩
    simp only [framesOf,List.length_append,iterate_add]
    change iterate _ (iterate _ _ 24) _ = _
    rw [eq,finish]; congr 1; push_cast; change t+24+_ = t+(24+_); omega

def clockPower (gates : Nat) := (6*gates-1).log2 + 1 + 2

def padded (gates : List (Gate ι)) : Code ι :=
  gates.map some ++ List.replicate (2^((6*gates.length-1).log2+1) - 6*gates.length) none

private theorem idle_length [DecidableEq ι] (n : Nat) :
    (framesOf (ι:=ι) (List.replicate n none)).length = 4*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,framesOf,List.length_append,ih,Nat.mul_succ]
    change 4+_ = _+4; omega

private theorem compiled_length [DecidableEq ι] (gates : List (Gate ι)) (tail : Code ι) :
    (framesOf (gates.map some ++ tail)).length = 24*gates.length + (framesOf tail).length := by
  induction gates with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons,List.cons_append,framesOf,List.length_append,ih,List.length_cons,Nat.mul_succ]
    change 24+_ = _; omega

theorem padded_length [DecidableEq ι] (gates : List (Gate ι)) :
    (framesOf (padded gates)).length = 2^(clockPower gates.length) := by
  rw [padded,compiled_length,idle_length,clockPower,Nat.pow_add 2 _ 2]
  change 24*_+4*_ = _*4
  have := Nat.lt_log2_self (n:=6*gates.length-1)
  omega

private theorem padded_exec [DecidableEq ι] (gs : List (Gate ι)) {x y : File ι}
    (h : Executes (gs.map some) x y) : Executes (padded gs) x y := by
  have append {c d : Code ι} {a b z : File ι} (u : Executes c a b) (v : Executes d b z) :
      Executes (c++d) a z := by
    induction u with
    | nil => exact v
    | idle _ ih => exact .idle (ih v)
    | gate hg _ ih => exact .gate hg (ih v)
  apply append h
  generalize (2^((6*gs.length-1).log2+1) - 6*gs.length) = n
  induction n with
  | zero => exact .nil _
  | succ n ih => exact .idle ih

def programMasks [DecidableEq ι] (gs : List (Gate ι)) (i : ι) : Table (clockPower gs.length) :=
  tableOf (framesOf (padded gs)) i

def compile [DecidableEq ι] (order : List ι) (gs : List (Gate ι)) (x : File ι) :=
  (seedBank _ (rowExps (programMasks gs) (biased ∘ x) order)).device false 0

theorem compiled_periods [DecidableEq ι] (order : List ι) (place : ∀ i, Placement order i)
    (gs : List (Gate ι)) (trace : Nat → File ι)
    (exec : ∀ n, Executes (gs.map some) (trace n) (trace (n+1))) (n : Nat) :
    let k := clockPower gs.length
    ∃ b : Bank k, iterate Device.advance (compile order gs (trace 0)) (n*2^k) =
      b.device false (n*(2^k:Nat) : Nat) ∧
      view b.regs = unitsView (rowExps (programMasks gs) (biased ∘ trace n) order) := by
  dsimp only
  induction n with
  | zero => exact ⟨_,by simp [compile,iterate],seed_view _⟩
  | succ n ih =>
    obtain ⟨b,checkpoint,bview⟩ := ih
    have h := frames_realized order place _ _ _ (padded_exec gs (exec n))
      (programMasks gs) b _ (table_matches _ (padded_length gs) n) bview
    rw [padded_length] at h
    obtain ⟨last,done,lastV⟩ := h
    refine ⟨last,?_,lastV⟩
    rw [Nat.succ_mul,iterate_add,checkpoint,done,Int.natCast_add]

/-! ## Equivalence between physical repetition and a finite register trajectory -/

def dataMeasure (xs : Exponents k) := (unitsView xs).map (fun x => x.2.word.length) |>.sum

private theorem columns_measure (cs : List (Column k)) (m : Table k) (tail : Memory k) :
    dataSize (columns m tail cs) = ((view cs).map (fun x => x.2.word.length)).sum := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih => simpa [dataSize,columns,view,List.map_map] using congrArg (c.data.word.length + ·) (ih c.mask)

private theorem cell_length (tile : Word) (n : Nat) : (tiles tile n).length = n*tile.length := by
  induction n with
  | zero => simp [tiles]
  | succ n ih => simp [tiles,ih,Nat.succ_mul,Nat.add_comm]

def fuelSize (order : List ι) (xs : File ι) := (order.map (fun i => 2^(biased (xs i))*8)).sum

private theorem fuel_measure (m : ι → Table k) (order : List ι) (xs : File ι) :
    dataMeasure (rowExps m (biased ∘ xs) order) = fuelSize order xs := by
  induction order with
  | nil => rfl
  | cons i order ih =>
    change (tiles (production b) _).length + _ = _ + _
    rw [cell_length]
    exact congrArg (_ + ·) ih

private theorem fuel_ge {order : List ι} (xs : File ι) {i : ι} (h : i ∈ order) :
    xs i ≤ fuelSize order xs := by
  induction order with
  | nil => simp at h
  | cons j js ih =>
    change xs i ≤ 2^(biased (xs j))*8 + fuelSize js xs
    cases List.mem_cons.mp h with
    | inl eq =>
      subst j
      have := Nat.lt_two_pow_self (n:=biased (xs i))
      unfold biased at *; omega
    | inr hm => have := ih hm; omega

def boundedFiles [DecidableEq ι] (bound : Nat) : List ι → List (File ι)
  | [] => [fun _ => 0]
  | i :: rest => (List.range (bound+1)).flatMap (fun n =>
      (boundedFiles bound rest).map (fun f j => if j = i then n else f j))

private theorem bounded_files_cover [DecidableEq ι] (order : List ι) (B : Nat) (f : File ι)
    (limited : ∀ i ∈ order, f i ≤ B) :
    ∃ g ∈ boundedFiles B order, ∀ i ∈ order, g i = f i := by
  induction order with
  | nil => exact ⟨fun _ => 0,by simp [boundedFiles],by simp⟩
  | cons i rest ih =>
    obtain ⟨g,hg,agree⟩ := ih (fun j h => limited j (List.mem_cons_of_mem _ h))
    refine ⟨fun j => if j = i then f i else g j,?_,?_⟩
    · exact List.mem_flatMap.mpr ⟨f i,List.mem_range.mpr (Nat.lt_succ_of_le (limited i (by simp))),
        List.mem_map.mpr ⟨g,hg,rfl⟩⟩
    · intro j hm; by_cases eq : j=i
      · simp [eq]
      · exact (if_neg eq).trans (agree _ ((List.mem_cons.mp hm).resolve_left eq))

theorem compiled_repeats_iff [DecidableEq ι] (order : List ι) (allRegs : ∀ i, i ∈ order)
    (place : ∀ i, Placement order i) (gs : List (Gate ι)) (trace : Nat → File ι)
    (exec : ∀ n, Executes (gs.map some) (trace n) (trace (n+1))) :
    Repeats (compile order gs (trace 0)).queue ↔ Covered trace := by
  let L := 2^(clockPower gs.length)
  have pos : 0 < L := Nat.two_pow_pos _
  rw [queue_repeats_iff_bounded_data _ (fun n => n*L) (fun _ _ lt => Nat.mul_lt_mul_of_pos_right lt pos)]
  have size (n : Nat) : dataSize (iterate Device.advance (compile order gs (trace 0)) (n*L)).blocks =
      fuelSize order (trace n) := by
    obtain ⟨bank,eq,hv⟩ := compiled_periods order place gs trace exec n
    rw [eq, bank_layout]
    change dataSize (columns _ _ _) = _
    rw [columns_measure,hv]
    exact fuel_measure _ _ _
  simp only [size]
  constructor
  · rintro ⟨B,h⟩
    refine ⟨boundedFiles B order,fun n => ?_⟩
    obtain ⟨g,hg,cover⟩ := bounded_files_cover order B (trace n)
      (fun i hi => Nat.le_trans (fuel_ge _ hi) (h n))
    exact (show g = trace n from funext (fun i => cover i (allRegs i))) ▸ hg
  · rintro ⟨files,allF⟩
    refine ⟨(files.map (fuelSize order)).sum,fun n => ?_⟩
    have bound (xs : List (File ι)) (mem : trace n ∈ xs) : fuelSize order (trace n) ≤ (xs.map (fuelSize order)).sum := by
      induction xs with
      | nil => simp at mem
      | cons f fs ih =>
        obtain eq | hm := List.mem_cons.mp mem
        · rw [eq]; simp
        · have := ih hm; simp; omega
    exact bound files (allF n)

/-! ## Compiling reversible counter-machine transitions -/

abbrev GatesRun [DecidableEq ι] (gs : List (Gate ι)) (x y : File ι) := Executes (gs.map some) x y

private theorem gates_append [DecidableEq ι] {gs hs : List (Gate ι)} {x y z : File ι}
    (h : GatesRun gs x y) (k : GatesRun hs y z) : GatesRun (gs++hs) x z := by
  have aux {cs ds : Code ι} {u v w : File ι} (hu : Executes cs u v) (hv : Executes ds v w) :
      Executes (cs++ds) u w := by
    induction hu with
    | nil => exact hv
    | idle _ ih => exact .idle (ih hv)
    | gate h _ ih => exact .gate h (ih hv)
  unfold GatesRun; rw [List.map_append]; exact aux h k

structure Enum (ι : Type) where
  items : List ι
  unique : items.Nodup
  complete : ∀ i, i ∈ items

private noncomputable def Enum.placement (u : Enum ι) (i : ι) : Placement u.items i := by
  classical
  have split := List.eq_append_cons_of_mem (u.complete i)
  let left := Classical.choose split
  let right := Classical.choose (Classical.choose_spec split)
  have spec := Classical.choose_spec (Classical.choose_spec split)
  have eq : u.items = left ++ i :: right := spec.1
  refine ⟨left,right,eq,spec.2,?_⟩
  have h := u.unique
  rw [eq] at h
  have tail : (i :: right).Nodup := List.Pairwise.sublist (List.suffix_append _ _).sublist h
  exact (List.nodup_cons.mp tail).1

def put [DecidableEq ι] (f : ι → α) (i : ι) (v : α) := fun j => if j=i then v else f j

@[simp] private theorem put_same [DecidableEq ι] (f : ι → α) (i : ι) (v : α) :
    put f i v i = v := by simp [put]

@[simp] private theorem put_other [DecidableEq ι] (f : ι → α) {j i : ι} (h : j ≠ i) (v : α) :
    put f i v j = f j := by simp [put,h]

@[simp] private theorem put_put [DecidableEq ι] (f : ι → α) (i : ι) (v w : α) :
    put (put f i v) i w = put f i w := by funext j; by_cases j=i <;> simp_all [put]

@[simp] private theorem put_id [DecidableEq ι] (f : ι → α) (i : ι) :
    put f i (f i) = f := by funext j; by_cases j=i <;> simp_all [put]

def single [DecidableEq ι] (ctrl dst : ι) (ch : Change) : Gate ι :=
  ⟨ctrl,fun i => if i=dst then ch else .stay⟩

private theorem single_run [DecidableEq ι] (f : File ι) {ctrl dst : ι} (ne : ctrl ≠ dst)
    (ch : Change) (safe : f ctrl = 0 → ch = .down → f dst > 0) :
    GatesRun [single ctrl dst ch] f
      (put f dst (if f ctrl = 0 then applyChange ch (f dst) else f dst)) := by
  have valid : (single ctrl dst ch).valid f := by
    intro i hz hdown
    by_cases eq : i=dst
    · subst i; exact safe hz (by simpa [single] using hdown)
    · simp [single,eq] at hdown
  have result : (single ctrl dst ch).update f =
      put f dst (if f ctrl = 0 then applyChange ch (f dst) else f dst) := by
    funext i; by_cases i=ctrl <;> by_cases i=dst <;> by_cases f ctrl=0 <;>
      simp_all [single,Gate.update,put,applyChange]
  exact .gate valid (result ▸ Executes.nil _)

inductive Predicate (ι : Type) where | always | positive (r : ι) | zero (r : ι)
def Predicate.holds (f : File ι) : Predicate ι → Bool
  | .always => true
  | .positive r => f r != 0
  | .zero r => f r == 0

def selectGates [DecidableEq ι] (zero flag latch : ι) (ch : Change) : Predicate ι → List (Gate ι)
  | .always => [single flag latch ch]
  | .positive r => [single r flag .up, single flag latch ch, single r flag .down]
  | .zero r => [single zero flag .up, single r flag .down, single flag latch ch,
                single r flag .up, single zero flag .down]

def Predicate.apart (pr : Predicate ι) (zero flag latch : ι) : Prop :=
  match pr with
  | .always => True
  | .positive r | .zero r => r ≠ flag ∧ r ≠ latch ∧ r ≠ zero

private theorem single_prepend [DecidableEq ι] {f y : File ι} {ctrl dst : ι} (ne : ctrl ≠ dst)
    (ch : Change) (safe : f ctrl = 0 → ch = .down → f dst > 0) {rest : List (Gate ι)}
    (run : GatesRun rest (put f dst (if f ctrl = 0 then applyChange ch (f dst) else f dst)) y) :
    GatesRun (single ctrl dst ch :: rest) f y := gates_append (single_run f ne ch safe) run

private theorem done_run [DecidableEq ι] {f g : File ι} (h : f=g) : GatesRun [] f g :=
  h ▸ Executes.nil f

private theorem select_run [DecidableEq ι] (f : File ι) {zero flag latch : ι}
    (hz : f zero = 0) (zf : zero ≠ flag) (zl : zero ≠ latch) (fl : flag ≠ latch)
    (pr : Predicate ι) (sep : pr.apart zero flag latch) (ch : Change)
    (safe : f flag = 0 → pr.holds f = true → ch = .down → f latch > 0) :
    GatesRun (selectGates zero flag latch ch pr) f
      (put f latch (if f flag = 0 ∧ pr.holds f = true then applyChange ch (f latch) else f latch)) := by
  cases pr with
  | always => simpa [selectGates,Predicate.holds] using single_run f fl ch (fun h => safe h rfl)
  | positive r =>
    obtain ⟨rf,rl,rz⟩ := sep
    unfold selectGates
    apply single_prepend rf _ (by simp)
    apply single_prepend fl _
    · by_cases z : f r=0 <;> simp [z,put,rf,fl,Ne.symm fl,applyChange]
      exact fun h => safe h (by simpa [Predicate.holds] using z)
    apply single_prepend rf _
    · by_cases z : f r=0 <;> simp [put,rf,rl,fl,Ne.symm fl,applyChange,z]
    apply done_run
    funext j
    by_cases z : f r=0 <;> by_cases ff : f flag=0 <;> by_cases jl : j=latch <;>
      by_cases jf : j=flag <;> simp_all [put,Predicate.holds,applyChange]
  | zero r =>
    obtain ⟨rf,rl,rz⟩ := sep
    unfold selectGates
    apply single_prepend zf _ (by simp)
    apply single_prepend rf _
    · simp [hz,applyChange]
    apply single_prepend fl _
    · by_cases z : f r=0 <;> simp [hz,z,rf,Ne.symm fl,applyChange]
      exact fun h => safe h (by simp [Predicate.holds,z])
    apply single_prepend rf _ (by simp)
    apply single_prepend zf _
    · simp [hz,rf,rl,zf,zl,Ne.symm fl,applyChange]; split <;> simp_all
    apply done_run
    funext j
    by_cases z : f r=0 <;> by_cases ff : f flag=0 <;> by_cases jl : j=latch <;>
      by_cases jf : j=flag <;> simp_all [put,Predicate.holds,applyChange]

inductive Op (R : Type) where
  | nop | inc (i : R) | dec (i : R) | testZ (i : R) | testP (i : R)
  deriving DecidableEq

def Op.inv : Op R → Op R
  | .inc r => .dec r
  | .dec r => .inc r
  | op => op

def Op.ready (x : File R) : Op R → Bool
  | .testZ i => x i == 0
  | .testP i | .dec i => x i != 0
  | _ => true

def Op.act [DecidableEq R] (x : File R) : Op R → File R
  | .inc i => put x i (x i+1)
  | .dec i => put x i (x i-1)
  | _ => x

private theorem undo_op [DecidableEq R] (op : Op R) (x : File R) (live : op.ready x = true) :
    op.inv.ready (op.act x) = true ∧ op.inv.act (op.act x) = x := by
  cases op <;> simp_all [Op.ready,Op.act,Op.inv,put_put]
  rename_i i
  have e : x i-1+1 = x i := by omega
  simp [e]

structure Config (Q R : Type) where
  pc : Q
  data : File R

structure Edge (Q R : Type) where
  src : Q
  op : Op R
  dest : Q

def Edge.inverse (u : Edge Q R) : Edge Q R := ⟨u.dest,u.op.inv,u.src⟩
def Edge.enabled (u : Edge Q R) (c : Config Q R) := c.pc = u.src ∧ u.op.ready c.data = true
def Edge.target [DecidableEq R] (u : Edge Q R) (c : Config Q R) : Config Q R :=
  ⟨u.dest,u.op.act c.data⟩

theorem edge_reverse [DecidableEq R] (u : Edge Q R) (c : Config Q R) (h : u.enabled c) :
    u.inverse.enabled (u.target c) ∧ u.inverse.target (u.target c) = c := by
  obtain ⟨live,undo⟩ := undo_op _ _ h.2
  exact ⟨⟨rfl,live⟩,by cases c; simp_all [Edge.target,Edge.inverse,Edge.enabled]⟩

inductive Reg (Q R E : Type) where | data (i : R) | pc (q : Q) | latch (i : E) | zero
  deriving DecidableEq

def pack [DecidableEq Q] (c : Config Q R) (latches : File E) : File (Reg Q R E)
  | .data i => c.data i
  | .pc q => if q=c.pc then 0 else 1
  | .latch i => latches i
  | .zero => 0

def Op.pred (op : Op R) : Predicate (Reg Q R E) :=
  match op with
  | .dec i | .testP i => .positive (.data i)
  | .testZ i => .zero (.data i)
  | _ => .always

private theorem pred_ready [DecidableEq Q] (op : Op R) (c : Config Q R) (ls : File E) :
    (op.pred (Q:=Q) (E:=E)).holds (pack c ls) = op.ready c.data := by cases op <;> rfl

def selection [DecidableEq Q] [DecidableEq R] [DecidableEq E] (u : Edge Q R) (i : E)
    (ch : Change) : List (Gate (Reg Q R E)) := selectGates .zero (.pc u.src) (.latch i) ch u.op.pred

private theorem selection_run [DecidableEq Q] [DecidableEq R] [DecidableEq E] (u : Edge Q R)
    (i : E) (ch : Change) (c : Config Q R) (ls : File E)
    (safe : u.enabled c → ch = .down → 0 < ls i) :
    GatesRun (selection u i ch) (pack c ls)
      (pack c (put ls i (if c.pc = u.src ∧ u.op.ready c.data = true then applyChange ch (ls i) else ls i))) := by
  have pc : pack c ls (.pc u.src) = 0 ↔ c.pc = u.src := by by_cases eq : c.pc=u.src <;> simp_all [pack,eq_comm]
  have h := select_run (pack c ls) (zero:=.zero) (flag:=.pc u.src) (latch:=.latch i)
    rfl (by simp) (by simp) (by simp) u.op.pred
    (by cases u.op <;> simp [Op.pred,Predicate.apart]) ch
    (fun flag ready => safe ⟨pc.mp flag, by rwa [pred_ready] at ready⟩)
  simp only [pc,pred_ready] at h
  have move (v : Nat) : put (pack c ls) (.latch i) v = pack c (put ls i v) := by
    funext j; cases j <;> simp [put,pack]
  rw [move] at h
  exact h
  
def Op.change [DecidableEq R] (op : Op R) (j : R) : Change :=
  match op with
  | .inc i => if j=i then .up else .stay
  | .dec i => if j=i then .down else .stay
  | _ => .stay

def applyGate [DecidableEq Q] [DecidableEq R] (u : Edge Q R) (i : E) : Gate (Reg Q R E) :=
  ⟨.latch i,fun
    | .pc q => if u.src = u.dest then .stay else if q = u.src then .up else if q = u.dest then .down else .stay
    | .data j => u.op.change j
    | _ => .stay⟩

private theorem apply_off [DecidableEq Q] [DecidableEq R] [DecidableEq E] (u : Edge Q R)
    (i : E) (c : Config Q R) (ls : File E) (inactive : ls i ≠ 0) :
    GatesRun [applyGate u i] (pack c ls) (pack c ls) := by
  have h : (applyGate u i).valid (pack c ls) := fun j zero => False.elim (inactive zero)
  have eq : (applyGate u i).update (pack c ls) = pack c ls := by
    funext j; simp [Gate.update,applyGate,pack,inactive]
  apply Executes.gate h; rw [eq]; exact .nil _

private theorem apply_on [DecidableEq Q] [DecidableEq R] [DecidableEq E] (u : Edge Q R)
    (i : E) (c : Config Q R) (ls : File E) (active : ls i = 0) (enabled : u.enabled c) :
    GatesRun [applyGate u i] (pack c ls) (pack (u.target c) ls) := by
  obtain ⟨pc,ready⟩ := enabled
  have h : (applyGate u i).valid (pack c ls) := by
    intro j _ down
    cases j with
    | latch j => contradiction
    | zero => contradiction
    | pc q =>
      change (if u.src=u.dest then _ else if q=u.src then _ else if q=u.dest then _ else _) = _ at down
      by_cases same : q=u.src <;> by_cases loop : u.src=u.dest <;> simp_all [pack,applyGate]
    | data j =>
      change u.op.change j = .down at down
      cases eq : u.op <;> simp [Op.change,eq] at down
      all_goals rename_i r; by_cases same : j=r <;> simp_all [Op.ready,pack] <;> omega
  have eq : (applyGate u i).update (pack c ls) = pack (u.target c) ls := by
    funext j
    cases j with
    | latch j => by_cases e : j=i <;> simp [applyGate,Gate.update,pack,active,e,applyChange]
    | zero => simp [applyGate,Gate.update,pack,active,applyChange]
    | pc q =>
      by_cases loop : u.src=u.dest <;> by_cases src : q=u.src <;> by_cases dst : q=u.dest <;>
        simp_all [Gate.update,applyGate,pack,Edge.target,applyChange]
    | data j =>
      cases h : u.op <;> simp [Gate.update,applyGate,pack,Edge.target,Op.act,Op.change,h,active,applyChange,put]
      all_goals rename_i r; by_cases same : j=r <;> simp [same,applyChange]
  apply Executes.gate h; rw [eq]; exact .nil _

private theorem scan_same [DecidableEq ι] (ls : List E) (emit : E → List (Gate ι)) (x : File ι)
    (same : ∀ j ∈ ls, GatesRun (emit j) x x) : GatesRun (ls.flatMap emit) x x := by
  induction ls with
  | nil => exact .nil _
  | cons j js ih => exact gates_append (same _ (by simp)) (ih (fun i hi => same i (by simp [hi])))

private theorem scan_selected [DecidableEq ι] (enum : Enum E) (i : E) (emit : E → List (Gate ι))
    (x y : File ι) (selected : GatesRun (emit i) x y)
    (before : ∀ j, j ≠ i → GatesRun (emit j) x x)
    (after : ∀ j, j ≠ i → GatesRun (emit j) y y) : GatesRun (enum.items.flatMap emit) x y := by
  let p := enum.placement i
  rw [p.split,List.flatMap_append,List.flatMap_cons]
  exact gates_append (scan_same _ _ _ (fun j hj => before j (fun eq => p.earlier (eq ▸ hj))))
    (gates_append selected (scan_same _ _ _ (fun j hj => after j (fun eq => p.later (eq ▸ hj)))))

private theorem select_off [DecidableEq Q] [DecidableEq R] [DecidableEq E] (u : Edge Q R)
    (i : E) (ch : Change) (c : Config Q R) (ls : File E) (off : ¬u.enabled c) :
    GatesRun (selection u i ch) (pack c ls) (pack c ls) := by
  have h := selection_run u i ch c ls (fun en => False.elim (off en))
  unfold Edge.enabled at off
  simpa only [if_neg off,put_id] using h

def program [DecidableEq Q] [DecidableEq R] [DecidableEq E] (enum : Enum E)
    (edges : E → Edge Q R) : List (Gate (Reg Q R E)) :=
  enum.items.flatMap (fun i => selection (edges i) i .down) ++
  enum.items.flatMap (fun i => [applyGate (edges i) i]) ++
  enum.items.flatMap (fun i => selection (edges i).inverse i .up)

def clean [DecidableEq Q] (c : Config Q R) : File (Reg Q R E) := pack c (fun _ => 1)

theorem one_period [DecidableEq Q] [DecidableEq R] [DecidableEq E] (enum : Enum E)
    (edges : E → Edge Q R) (c : Config Q R) (i : E) (enabled : (edges i).enabled c)
    (forward : ∀ j, (edges j).enabled c → j = i)
    (backward : ∀ j, (edges j).inverse.enabled ((edges i).target c) → j = i) :
    GatesRun (program enum edges) (clean c) (clean ((edges i).target c)) := by
  let ls : File E := fun _ => 1
  let mark := put ls i 0
  let dest := (edges i).target c
  have en : c.pc = (edges i).src ∧ (edges i).op.ready c.data = true := enabled
  have inv : (edges i).inverse.enabled dest := (edge_reverse _ _ enabled).1
  have sel := selection_run (edges i) i .down c ls (by intros; exact Nat.zero_lt_succ _)
  have clear := selection_run (edges i).inverse i .up dest mark (by simp)
  have marked : GatesRun (selection (edges i) i .down) (pack c ls) (pack c mark) := by
    simpa [en.1,en.2,mark,ls,applyChange] using sel
  have cleared : GatesRun (selection (edges i).inverse i .up) (pack dest mark) (pack dest ls) := by
    have reset : put mark i 1 = ls := by
      change put (put ls i 0) i (ls i) = ls; simp
    unfold Edge.enabled at inv
    simpa only [if_pos inv,show mark i = 0 from put_same _ _ _,applyChange,Nat.zero_add,reset] using clear
  have off (j : E) (ne : j ≠ i) (l : File E) :=
    select_off (edges j) j .down c l (fun h => ne (forward j h))
  have offInv (j : E) (ne : j ≠ i) (l : File E) :=
    select_off (edges j).inverse j .up dest l (fun h => ne (backward j h))
  have on := apply_on (edges i) i c mark (put_same _ _ _) enabled
  have offApply (j : E) (ne : j ≠ i) (conf : Config Q R) :
      GatesRun [applyGate (edges j) j] (pack conf mark) (pack conf mark) :=
    apply_off _ _ _ _ (by simp [mark,ne,ls])
  exact gates_append (gates_append
    (scan_selected enum i _ _ _ marked (fun j h => off j h ls) (fun j h => off j h mark))
    (scan_selected enum i (fun j => [applyGate (edges j) j]) _ _ on
      (fun j h => offApply j h c) (fun j h => offApply j h dest)))
    (scan_selected enum i _ _ _ cleared (fun j h => offInv j h mark) (fun j h => offInv j h ls))

/-! ## Finite machine descriptions and reverse execution -/

private def distinctList [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then distinctList xs else x :: distinctList xs

private theorem mem_distinctList [DecidableEq α] (xs : List α) (x : α) :
    x ∈ distinctList xs ↔ x ∈ xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    simp only [distinctList]
    split
    · rename_i h; simp [ih]; intro eq; exact eq ▸ h
    · simp [ih]

private theorem nodup_distinctList [DecidableEq α] (xs : List α) : (distinctList xs).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons v vs ih => simp only [distinctList]; split <;> simp_all [List.nodup_cons,mem_distinctList]

def makeEnum [DecidableEq α] (xs : List α) (complete : ∀ i, i ∈ xs) : Enum α :=
  ⟨distinctList xs,nodup_distinctList xs,fun i => (mem_distinctList _ _).mpr (complete i)⟩

def registerEnum [DecidableEq Q] [DecidableEq R] [DecidableEq E]
    (qs : Enum Q) (rs : Enum R) (es : Enum E) : Enum (Reg Q R E) :=
  makeEnum (rs.items.map Reg.data ++ qs.items.map Reg.pc ++ es.items.map Reg.latch ++ [.zero])
    (by intro i; cases i <;> simp [qs.complete,rs.complete,es.complete])

inductive BounceId (E : Type) where | fwd (i : E) | rev (i : E) | turnH | turnS
  deriving DecidableEq

def bounceEnum [DecidableEq E] (es : Enum E) : Enum (BounceId E) :=
  makeEnum (es.items.map BounceId.fwd ++ es.items.map BounceId.rev ++ [.turnH,.turnS])
    (by intro i; cases i <;> simp [es.complete])

def dirEnum [DecidableEq Q] (qs : Enum Q) : Enum (Bool × Q) :=
  makeEnum (qs.items.map (false,·) ++ qs.items.map (true,·))
    (by rintro ⟨p,i⟩; cases p <;> simp [qs.complete])

structure Machine (Q R E : Type) where
  states : Enum Q
  regs : Enum R
  edges : Enum E
  instruction : E → Edge Q R
  entry : Q
  halt : Q

def directed (p : Bool) (c : Config Q R) : Config (Bool × Q) R := ⟨(p,c.pc),c.data⟩
def liftEdge (p : Bool) (op : Edge Q R) : Edge (Bool × Q) R := ⟨(p,op.src),op.op,(p,op.dest)⟩
def bounced (m : Machine Q R E) : BounceId E → Edge (Bool × Q) R
  | .fwd i => liftEdge false (m.instruction i)
  | .rev i => liftEdge true (m.instruction i).inverse
  | .turnH => ⟨(false,m.halt),.nop,(true,m.halt)⟩
  | .turnS => ⟨(true,m.entry),.nop,(false,m.entry)⟩

-- All restrictions concern the finite source machine. No hypothesis refers
-- to tag words, the compiler, physical time, or a checkpoint invariant.
structure Reversible (m : Machine Q R E) : Prop where
  fresh : ∀ i, (m.instruction i).dest ≠ m.entry
  terminal : ∀ i, (m.instruction i).src ≠ m.halt
  deterministic : ∀ c i j, (m.instruction i).enabled c → (m.instruction j).enabled c → i=j
  backward : ∀ c i j, (m.instruction i).inverse.enabled c → (m.instruction j).inverse.enabled c → i=j

private theorem inv_inv (u : Edge Q R) : u.inverse.inverse = u := by
  obtain ⟨src,op,dest⟩ := u
  cases op <;> rfl

private theorem enabled_lift (p q : Bool) (u : Edge Q R) (c : Config Q R) :
    (liftEdge p u).enabled (directed q c) ↔ q=p ∧ u.enabled c := by
  simp [Edge.enabled,liftEdge,directed,and_assoc]

private theorem inverse_lift (p : Bool) (u : Edge Q R) :
    (liftEdge p u).inverse = liftEdge p u.inverse := rfl

private theorem bounce_unique (m : Machine Q R E) (rev : Reversible m)
    (c : Config (Bool × Q) R) (i j : BounceId E) (hi : (bounced m i).enabled c)
    (hj : (bounced m j).enabled c) : i=j := by
  obtain ⟨⟨p,q⟩,data⟩ := c
  change (bounced m i).enabled (directed p ⟨q,data⟩) at hi
  change (bounced m j).enabled (directed p ⟨q,data⟩) at hj
  cases i <;> cases j <;> simp only [bounced,enabled_lift] at hi hj <;>
    simp only [Edge.enabled,directed,Edge.inverse, Prod.mk.injEq,Op.ready,and_true] at hi hj
  all_goals first
    | rfl
    | exact congrArg BounceId.fwd (rev.deterministic ⟨q,data⟩ _ _ hi.2 hj.2)
    | exact congrArg BounceId.rev (rev.backward ⟨q,data⟩ _ _ hi.2 hj.2)
    | exfalso; apply rev.fresh _; exact hi.2.1.symm.trans hj.2
    | exfalso; apply rev.fresh _; exact hj.2.1.symm.trans hi.2
    | exfalso; apply rev.terminal _; exact hi.2.1.symm.trans hj.2
    | exfalso; apply rev.terminal _; exact hj.2.1.symm.trans hi.2
    | simp_all

def BounceId.flip : BounceId E → BounceId E
  | .fwd i => .rev i
  | .rev i => .fwd i
  | .turnH => .turnH
  | .turnS => .turnS

private theorem flip_live (m : Machine Q R E) (i : BounceId E) (p : Bool) (c : Config Q R) :
    (bounced m i).inverse.enabled (directed p c) ↔ (bounced m i.flip).enabled (directed (!p) c) := by
  cases i <;> cases p <;> simp only [BounceId.flip,bounced,inverse_lift,enabled_lift,inv_inv] <;>
    simp [Edge.enabled,Edge.inverse,directed,Op.ready,Op.inv]

private theorem bounce_backward (m : Machine Q R E) (rev : Reversible m)
    (c : Config (Bool × Q) R) (i j : BounceId E) (hi : (bounced m i).inverse.enabled c)
    (hj : (bounced m j).inverse.enabled c) : i=j := by
  obtain ⟨⟨p,q⟩,data⟩ := c
  have eq := bounce_unique m rev _ _ _ ((flip_live m i p ⟨q,data⟩).mp hi)
    ((flip_live m j p ⟨q,data⟩).mp hj)
  have twice (u : BounceId E) : u.flip.flip = u := by cases u <;> rfl
  simpa only [twice] using congrArg BounceId.flip eq

def Machine.lookup [DecidableEq Q] (m : Machine Q R E) (c : Config Q R) :=
  m.edges.items.find? (fun i => decide (c.pc = (m.instruction i).src) && (m.instruction i).op.ready c.data)

def Machine.next [DecidableEq Q] [DecidableEq R] (m : Machine Q R E) (c : Config Q R) :=
  (m.lookup c).map (fun i => (m.instruction i).target c)

def Machine.path [DecidableEq Q] [DecidableEq R] (m : Machine Q R E) (input : File R) :=
  iterate (fun c => (m.next c).getD c) ⟨m.entry,input⟩

def Machine.live [DecidableEq Q] [DecidableEq R] (m : Machine Q R E) (input : File R) :=
  ∀ n, (m.path input n).pc ≠ m.halt → ∃ i, (m.instruction i).enabled (m.path input n)

private theorem next_edge [DecidableEq Q] [DecidableEq R] {m : Machine Q R E}
    {c d : Config Q R} (step : m.next c = some d) :
    ∃ i, (m.instruction i).enabled c ∧ (m.instruction i).target c = d := by
  unfold Machine.next at step
  cases e : m.lookup c with
  | none => simp [e] at step
  | some i =>
    have ok := List.find?_some e
    refine ⟨i,?_,by simpa [e] using step⟩
    simpa [Edge.enabled] using ok

private theorem path_edge [DecidableEq Q] [DecidableEq R] (m : Machine Q R E) (input : File R)
    (live : m.live input) (n : Nat) (nonhalt : (m.path input n).pc ≠ m.halt) :
    ∃ i, (m.instruction i).enabled (m.path input n) ∧
      (m.instruction i).target (m.path input n) = m.path input (n+1) := by
  let c := m.path input n
  cases e : m.lookup c with
  | none =>
    obtain ⟨i,he⟩ := live n nonhalt
    have bad := List.find?_eq_none.mp e i (m.edges.complete i)
    exact False.elim (bad (by simpa [c,Edge.enabled] using he))
  | some i =>
    apply next_edge
    change m.next c = some ((m.next c).getD c)
    simp [Machine.next,e]

private theorem bounce_prefix (stop : Nat → Bool) (n : Nat) :
    ∀ j, j < (bounce stop n).1 → stop j = false := by
  induction n with
  | zero => simp [bounce]
  | succ n ih =>
    cases eq : bounce stop n with
    | mk k back =>
      rw [eq] at ih
      intro j hj
      simp only [bounce,eq] at hj
      cases back <;> simp at hj
      · cases hs : stop k <;> simp [hs] at hj
        · by_cases j=k
          · subst j; exact hs
          · apply ih; omega
        · exact ih j hj
      · apply ih; omega

def Machine.stop [DecidableEq Q] [DecidableEq R] (m : Machine Q R E) (input : File R) (n : Nat) :=
  decide ((m.path input n).pc = m.halt)

def Machine.atCheckpoint [DecidableEq Q] [DecidableEq R] (m : Machine Q R E) (input : File R)
    (n : Nat) :=
  let pos := bounce (m.stop input) n
  directed pos.2 (m.path input pos.1)

private theorem checkpoint_edge [DecidableEq Q] [DecidableEq R] (m : Machine Q R E) (input : File R)
    (live : m.live input) (n : Nat) :
    ∃ i, (bounced m i).enabled (m.atCheckpoint input n) ∧
      (bounced m i).target (m.atCheckpoint input n) = m.atCheckpoint input (n+1) := by
  let stop := m.stop input
  let path := m.path input
  change ∃ i, (bounced m i).enabled (directed (bounce stop n).2 (path (bounce stop n).1)) ∧
    (bounced m i).target (directed (bounce stop n).2 (path (bounce stop n).1)) =
    directed (bounce stop (n+1)).2 (path (bounce stop (n+1)).1)
  cases eq : bounce stop n with
  | mk k back =>
    simp only [bounce,eq]
    cases back with
    | false =>
      cases hs : stop k with
      | true =>
        have halt : (path k).pc = m.halt := by simpa [stop,Machine.stop,path] using hs
        refine ⟨.turnH,?_,?_⟩ <;> simp [bounced,directed,Edge.enabled,Edge.target,hs,halt,Op.ready,Op.act]
      | false =>
        have notH : (path k).pc ≠ m.halt := by simpa [stop,Machine.stop,path] using hs
        obtain ⟨i,go,dest⟩ := path_edge m input live k notH
        refine ⟨.fwd i,?_,?_⟩
        · exact (enabled_lift _ _ _ _).mpr ⟨rfl,go⟩
        · simp only [hs,Bool.false_eq_true,if_false]
          exact congrArg (directed false) dest
    | true =>
      cases k with
      | zero =>
        refine ⟨.turnS,?_,?_⟩
        · exact ⟨rfl,rfl⟩
        · rfl
      | succ j =>
        have pre := bounce_prefix stop n j (by rw [eq]; exact Nat.lt_succ_self _)
        obtain ⟨i,go,dest⟩ := path_edge m input live j (by simpa [stop,Machine.stop] using pre)
        obtain ⟨rev,undo⟩ := edge_reverse _ _ go
        rw [dest] at rev undo
        refine ⟨.rev i,?_,?_⟩
        · exact (enabled_lift _ _ _ _).mpr ⟨rfl,rev⟩
        · exact congrArg (directed true) undo

private theorem next_fresh [DecidableEq Q] [DecidableEq R] (m : Machine Q R E)
    (rev : Reversible m) (c : Config Q R) (input : File R) :
    m.next c ≠ some ⟨m.entry,input⟩ := by
  intro eq
  obtain ⟨i,_,hd⟩ := next_edge eq
  exact rev.fresh i (congrArg Config.pc hd)

private theorem next_injective [DecidableEq Q] [DecidableEq R] (m : Machine Q R E)
    (rev : Reversible m) (x y dest : Config Q R)
    (hx : m.next x = some dest) (hy : m.next y = some dest) : x=y := by
  obtain ⟨i,go,dx⟩ := next_edge hx
  obtain ⟨j,go',dy⟩ := next_edge hy
  obtain ⟨ix,undo⟩ := edge_reverse _ _ go
  obtain ⟨jy,undo'⟩ := edge_reverse _ _ go'
  rw [dx] at ix undo
  rw [dy] at jy undo'
  have eq := rev.backward dest i j ix jy
  subst j
  exact undo.symm.trans undo'

private theorem clean_injective [DecidableEq Q] {x y : Config Q R}
    (h : clean (E:=E) x = clean y) : x=y := by
  have pc := congrFun h (.pc x.pc)
  by_cases eq : x.pc = y.pc
  · have values := funext (fun i => congrFun h (.data i))
    cases x; cases y; congr
  · simp [clean,pack,eq] at pc

def encodedDevice [DecidableEq Q] [DecidableEq R] [DecidableEq E] (m : Machine Q R E)
    (input : File R) :=
  let be := bounceEnum m.edges
  let regs := registerEnum (dirEnum m.states) m.regs be
  compile regs.items (program be (bounced m)) (clean (E:=BounceId E) (directed false ⟨m.entry,input⟩))

/-! ## Executable encoder and the end-to-end theorem -/

-- Compute all initial differences by adjacent XORs. A direct recursive
-- evaluation of delta at depth L would re-evaluate the same bits exponentially.
def past (m : Mask) (t : Int) : Nat → List Bool
  | 0 => []
  | n+1 => m t :: past m (t-1) n

def adjacent : List Bool → List Bool
  | x :: y :: xs => (x ^^ y) :: adjacent (y :: xs)
  | _ => []

private theorem adjacent_past (m : Mask) (t : Int) (n : Nat) :
    adjacent (past m t (n+1)) = past (delta m) t n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => exact congrArg ((delta m t) :: ·) (ih (t-1))

def clockFromBits : List Bool → List Bool → Word
  | [], _ => []
  | s :: ss, bits => differentiator s ++ clockFromBits ss (adjacent bits) ++
      integrator (s ^^ bits.headD false)

theorem clockFromBits_correct (ss : List Bool) (m : Mask) (t : Int) :
    clockFromBits ss (past m (t-1) ss.length) = clockWord m t ss := by
  induction ss generalizing m with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.length_cons,clockFromBits,adjacent_past,ih,clockWord]
    rfl

def serializeBlock (t : Int) : Block k → Word
  | .data d => d.word
  | .clock c => clockFromBits c.memory (past (periodMask k c.bits) (t-1) c.memory.length)

def serialize (d : Device k) : Word := cutWord d.cut (d.blocks.flatMap (serializeBlock d.time))

private theorem serialize_correct (d : Device k) : serialize d = d.word := by
  have ok (blocks : List (Block k)) : blocks.flatMap (serializeBlock d.time) = layoutWord d.time blocks := by
    induction blocks with
    | nil => rfl
    | cons v vs ih => cases v <;> simp [serializeBlock,Block.word,clockFromBits_correct,layoutWord,ih]
  exact congrArg (cutWord d.cut) (ok _)

def encode [DecidableEq Q] [DecidableEq R] [DecidableEq E] (m : Machine Q R E)
    (input : File R) : Word := serialize (encodedDevice m input)

def ExactCycle (w : Word) : Prop :=
  ∃ i j v, i < j ∧ runSteps i w = some v ∧ runSteps j w = some v

private theorem device_cycle (d : Device k) : ExactCycle d.word ↔ Repeats d.queue := by
  constructor
  · rintro ⟨i,j,v,lt,hi,hj⟩
    exact ⟨i,j,lt,by simp [Device.queue,hi,hj]⟩
  · rintro ⟨i,j,lt,eq⟩
    obtain ⟨v,hi⟩ := device_live d i
    obtain ⟨u,hj⟩ := device_live d j
    have eq' : v=u := by simpa [Device.queue,hi,hj] using eq
    exact ⟨i,j,v,lt,hi,eq' ▸ hj⟩

/-- End-to-end reduction for a finite reversible counter machine, starting
at its entry with the supplied registers. The right side uses only the
computed finite input and literal, successful six-symbol tag steps. -/
theorem halt_iff_exact_cycle [DecidableEq Q] [DecidableEq R] [DecidableEq E]
    (m : Machine Q R E) (input : File R) (rev : Reversible m) (live : m.live input) :
    (∃ n, (m.path input n).pc = m.halt) ↔ ExactCycle (encode m input) := by
  let be := bounceEnum m.edges
  let regs := registerEnum (dirEnum m.states) m.regs be
  let gs := program be (bounced m)
  let trace := fun n => clean (E:=BounceId E) (m.atCheckpoint input n)
  have executes (n : Nat) : GatesRun gs (trace n) (trace (n+1)) := by
    obtain ⟨i,enabled,dest⟩ := checkpoint_edge m input live n
    have h := one_period be (bounced m) _ i enabled
      (fun j go => bounce_unique m rev _ j i go enabled)
      (fun j go => bounce_backward m rev _ j i go (edge_reverse _ _ enabled).1)
    rw [dest] at h
    exact h
  rw [encode,serialize_correct]
  change _ ↔ ExactCycle (compile regs.items gs (trace 0)).word
  rw [device_cycle,compiled_repeats_iff regs.items regs.complete regs.placement gs trace executes]
  constructor
  · rintro ⟨n,hit⟩
    let atPos (k : Nat) (back : Bool) := clean (E:=BounceId E) (directed back (m.path input k))
    refine ⟨(List.range (n+1)).flatMap (fun k => [atPos k false,atPos k true]),?_⟩
    intro j
    let pos := bounce (m.stop input) j
    have lim : pos.1 ≤ n := bounce_bounded _ (by simpa [Machine.stop] using hit) j
    refine List.mem_flatMap.mpr ⟨pos.1,List.mem_range.mpr (Nat.lt_succ_of_le lim),?_⟩
    change atPos pos.1 pos.2 ∈ [_,_]
    cases pos.2 <;> simp
  · intro finite
    apply Classical.byContradiction
    intro miss
    have live' (n : Nat) : (m.path input n).pc ≠ m.halt := fun h => miss ⟨n,h⟩
    have noStop (n : Nat) : m.stop input n = false := by simp [Machine.stop,live']
    have moves (n : Nat) : m.next (m.path input n) = some (m.path input (n+1)) := by
      obtain ⟨i,go,_⟩ := path_edge m input live n (live' n)
      let c := m.path input n
      change m.next c = some ((m.next c).getD c)
      cases eq : m.lookup c with
      | some _ => simp [Machine.next,eq]
      | none =>
        have bad := List.find?_eq_none.mp eq i (m.edges.complete i)
        exact False.elim (bad (by simpa [Edge.enabled,c] using go))
    obtain ⟨i,j,lt,same⟩ := repeats_of_covered finite
    have sameConfig := clean_injective same
    change directed _ _ = directed _ _ at sameConfig
    simp only [always_forward noStop] at sameConfig
    have equalSource : m.path input i = m.path input j := by
      exact congrArg (fun c : Config (Bool × Q) R => (⟨c.pc.2,c.data⟩ : Config Q R)) sameConfig
    exact fresh_path m.next (fun c => next_fresh m rev c input) (next_injective m rev)
      moves i j lt equalSource

#print axioms halt_iff_exact_cycle
#print axioms encode

/-! ## A program with halting and nonhalting inputs -/

namespace Example

inductive State where | entry | loop | halt
  deriving DecidableEq, Repr

inductive Label where | zero | pos | count
  deriving DecidableEq, Repr

-- From entry, zero enters an incrementing loop and a positive input halts.
def machine : Machine State Unit Label where
  states := ⟨[.entry,.loop,.halt],by decide,by intro i; cases i <;> decide⟩
  regs := ⟨[()],by decide,by intro i; cases i; decide⟩
  edges := ⟨[.zero,.pos,.count],by decide,by intro i; cases i <;> decide⟩
  instruction
    | .zero => ⟨.entry,.testZ (),.loop⟩
    | .pos => ⟨.entry,.testP (),.halt⟩
    | .count => ⟨.loop,.inc (),.loop⟩
  entry := .entry
  halt := .halt

private theorem reversible : Reversible machine := by
  constructor
  · intro i; cases i <;> decide
  · intro i; cases i <;> decide
  · rintro ⟨pc,x⟩ i j; cases pc <;> cases i <;> cases j <;>
      simp [Edge.enabled,machine,Op.ready]
  · rintro ⟨pc,x⟩ i j; cases pc <;> cases i <;> cases j <;>
      simp [Edge.enabled,machine,Edge.inverse,Op.inv,Op.ready]

private theorem live (x : Nat) : machine.live (fun _ => x) := by
  intro n running
  generalize eq : machine.path (fun _ => x) n = c at *
  cases c with
  | mk pc regs =>
    cases pc with
    | entry =>
      by_cases h : regs () = 0
      · exact ⟨.zero,⟨rfl,by simpa [machine,Op.ready] using h⟩⟩
      · exact ⟨.pos,⟨rfl,by simpa [machine,Op.ready] using h⟩⟩
    | loop => exact ⟨.count,rfl,rfl⟩
    | halt => exact False.elim (running rfl)

theorem input_positive_iff_cycle (x : Nat) :
    0 < x ↔ ExactCycle (encode machine (fun _ => x)) := by
  rw [← halt_iff_exact_cycle _ _ reversible (live x)]
  constructor
  · intro pos
    refine ⟨1,?_⟩
    cases x with
    | zero => omega
    | succ x => rfl
  · rintro ⟨n,halted⟩
    cases x with
    | succ x => omega
    | zero =>
      have looping (n : Nat) : (machine.path (fun _ => 0) (n+1)).pc = .loop := by
        induction n with
        | zero => rfl
        | succ n ih =>
          let c := machine.path (fun _ => 0) (n+1)
          have pick : machine.lookup c = some .count := by
            change c.pc = .loop at ih
            simp [Machine.lookup,machine,List.find?,ih,Op.ready]
          change ((machine.next c).getD c).pc = .loop
          unfold Machine.next; rw [pick]; rfl
      cases n with
      | zero => contradiction
      | succ n => rw [looping] at halted; contradiction

#print axioms input_positive_iff_cycle

end Example

end SixSymbol
