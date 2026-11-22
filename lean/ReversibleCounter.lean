import SixSymbol

/-!
# From deterministic counter machines to the six-symbol theorem

`SixSymbol.halt_iff_exact_cycle` assumes a reversible source machine whose run
never gets stuck before halt. This file discharges both assumptions for every
ordinary deterministic counter machine whose nonhalting states always have an
applicable instruction. Such machines (Minsky's normal form) are universal.

The construction keeps a history register `hist` and a work register `work`.
Each source step `e` is followed by a gadget that replaces `hist` by
`(N+1)·hist + (N+1-idx e)`, where `N` is the number of source edges. Different
edges entering the same state enter a shared multiplication loop at different
points, which is what makes the simulation backward deterministic.

The main theorem is `ReversibleCounter.halt_iff_exact_cycle`.
-/

namespace ReversibleCounter
open SixSymbol

set_option linter.unusedSectionVars false

/-! ## List positions and finite ranges -/

def pos [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: ys => if x = y then 0 else pos x ys + 1

theorem pos_lt [DecidableEq α] {x : α} : ∀ {l : List α}, x ∈ l → pos x l < l.length
  | [], h => by cases h
  | y :: ys, h => by
    by_cases xy : x = y
    · simp [pos, xy]
    · simpa [pos, xy] using Nat.succ_lt_succ (pos_lt ((List.mem_cons.mp h).resolve_left xy))

theorem pos_inj [DecidableEq α] {x y : α} :
    ∀ {l : List α}, x ∈ l → y ∈ l → pos x l = pos y l → x = y
  | [], h, _, _ => by cases h
  | z :: zs, hx, hy, eq => by
    simp only [pos] at eq
    by_cases xz : x = z <;> by_cases yz : y = z
    · exact xz.trans yz.symm
    · rw [if_pos xz, if_neg yz] at eq; omega
    · rw [if_neg xz, if_pos yz] at eq; omega
    · rw [if_neg xz, if_neg yz] at eq
      exact pos_inj ((List.mem_cons.mp hx).resolve_left xz)
        ((List.mem_cons.mp hy).resolve_left yz) (by omega)

def fins : (n : Nat) → List (Fin n)
  | 0 => []
  | n+1 => 0 :: (fins n).map Fin.succ

theorem mem_fins : ∀ {n : Nat} (k : Fin n), k ∈ fins n
  | 0, k => k.elim0
  | n+1, k => by
    refine Fin.cases ?_ (fun j => ?_) k
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_fins j))

/-! ## Source machines -/

variable {Q R E : Type} [DecidableEq Q] [DecidableEq R] [DecidableEq E]

/-- An ordinary deterministic counter machine with a fresh entry, a terminal
halt, and an applicable instruction at every nonhalting configuration. -/
structure Standard (m : Machine Q R E) : Prop where
  fresh : ∀ i, (m.instruction i).dest ≠ m.entry
  terminal : ∀ i, (m.instruction i).src ≠ m.halt
  deterministic : ∀ c i j, (m.instruction i).enabled c → (m.instruction j).enabled c → i = j
  total : ∀ c : Config Q R, c.pc ≠ m.halt → ∃ i, (m.instruction i).enabled c

theorem lookup_enabled {m : Machine Q R E} {c : Config Q R} {i : E}
    (h : m.lookup c = some i) : (m.instruction i).enabled c :=
  Machine.lookup_enabled h

theorem next_edge' {m : Machine Q R E} {c d : Config Q R} (h : m.next c = some d) :
    ∃ i, (m.instruction i).enabled c ∧ (m.instruction i).target c = d :=
  Machine.next_edge h

theorem next_of_enabled {m : Machine Q R E}
    (det : ∀ c i j, (m.instruction i).enabled c → (m.instruction j).enabled c → i = j)
    {c : Config Q R} {i : E} (h : (m.instruction i).enabled c) :
    m.next c = some ((m.instruction i).target c) := by
  have look : m.lookup c = some i := by
    cases e : m.lookup c with
    | none => exact (Machine.lookup_ne_none h e).elim
    | some j => rw [det c j i (lookup_enabled e) h]
  simp [Machine.next, look]

/-- A property preserved by every enabled edge holds along the whole run. -/
theorem path_invariant (m : Machine Q R E) (input : File R) (P : Config Q R → Prop)
    (start : P ⟨m.entry, input⟩)
    (pres : ∀ c i, P c → (m.instruction i).enabled c → P ((m.instruction i).target c)) :
    ∀ n, P (m.path input n) := by
  intro n
  induction n with
  | zero => exact start
  | succ n ih =>
    change P ((m.next (m.path input n)).getD (m.path input n))
    cases e : m.next (m.path input n) with
    | none => exact ih
    | some d =>
      obtain ⟨i, go, hd⟩ := next_edge' e
      exact hd ▸ pres _ i ih go

theorem path_succ {m : Machine Q R E}
    (det : ∀ c i j, (m.instruction i).enabled c → (m.instruction j).enabled c → i = j)
    {input : File R} {n : Nat} {i : E} (h : (m.instruction i).enabled (m.path input n)) :
    m.path input (n+1) = (m.instruction i).target (m.path input n) := by
  change (m.next (m.path input n)).getD (m.path input n) = _
  rw [next_of_enabled det h]; rfl

/-! ## The reversible machine -/

inductive Slot (R : Type) where
  | orig (r : R) | hist | work
  deriving DecidableEq

/-- Gadget states. `P` holds the source states other than entry. -/
inductive Node (Q P E : Type) (N : Nat) where
  | base (q : Q)
  | mid (e : E) | tr (e : E) | trInc (e : E)
  | a (q : P) (k : Fin (N+1)) | b (q : P) (k : Fin (N+1))
  | top (q : P) | pre (q : P)
  deriving DecidableEq

inductive Move (P E : Type) (N : Nat) where
  | lift (e : E) | enter (e : E) | trExit (e : E) | trDec (e : E) | trInc (e : E)
  | aInc (q : P) (k : Fin (N+1)) | bStep (q : P) (k : Fin N) | bLast (q : P)
  | topExit (q : P) | topDec (q : P) | preGo (q : P)
  deriving DecidableEq

def liftOp : Op R → Op (Slot R)
  | .nop => .nop
  | .inc i => .inc (.orig i)
  | .dec i => .dec (.orig i)
  | .testZ i => .testZ (.orig i)
  | .testP i => .testP (.orig i)

def proj (f : File (Slot R)) : File R := fun r => f (.orig r)

variable (m : Machine Q R E)

abbrev Live := {q : Q // q ≠ m.entry}
abbrev width := m.edges.items.length
abbrev RNode := Node Q (Live m) E (width m)
abbrev RMove := Move (Live m) E (width m)

def idx (e : E) : Fin (width m + 1) :=
  ⟨pos e m.edges.items, Nat.lt_succ_of_lt (pos_lt (m.edges.complete e))⟩

def move (fresh : ∀ i, (m.instruction i).dest ≠ m.entry) :
    RMove m → Edge (RNode m) (Slot R)
  | .lift e => ⟨.base (m.instruction e).src, liftOp (m.instruction e).op, .mid e⟩
  | .enter e => ⟨.mid e, .testZ .work, .tr e⟩
  | .trExit e => ⟨.tr e, .testZ .hist, .a ⟨(m.instruction e).dest, fresh e⟩ (idx m e)⟩
  | .trDec e => ⟨.tr e, .dec .hist, .trInc e⟩
  | .trInc e => ⟨.trInc e, .inc .work, .tr e⟩
  | .aInc q k => ⟨.a q k, .inc .hist, .b q k⟩
  | .bStep q k => ⟨.b q k.castSucc, .testP .hist, .a q k.succ⟩
  | .bLast q => ⟨.b q (Fin.last _), .testP .hist, .top q⟩
  | .topExit q => ⟨.top q, .testZ .work, .base q.val⟩
  | .topDec q => ⟨.top q, .dec .work, .pre q⟩
  | .preGo q => ⟨.pre q, .testP .hist, .a q 0⟩

def lives : List (Live m) :=
  m.states.items.filterMap (fun q => if h : q = m.entry then none else some ⟨q, h⟩)

theorem mem_lives (q : Live m) : q ∈ lives m := by
  refine List.mem_filterMap.mpr ⟨q.val, m.states.complete _, ?_⟩
  simp [q.property]

def rev (fresh : ∀ i, (m.instruction i).dest ≠ m.entry) :
    Machine (RNode m) (Slot R) (RMove m) where
  states := makeEnum
    (m.states.items.map .base ++ m.edges.items.map .mid ++ m.edges.items.map .tr ++
      m.edges.items.map .trInc ++
      (lives m).flatMap (fun q => (fins _).map (.a q)) ++
      (lives m).flatMap (fun q => (fins _).map (.b q)) ++
      (lives m).map .top ++ (lives m).map .pre)
    (by
      intro i
      cases i <;> simp [m.states.complete, m.edges.complete, mem_lives, mem_fins])
  regs := makeEnum (m.regs.items.map .orig ++ [.hist, .work])
    (by intro i; cases i <;> simp [m.regs.complete])
  edges := makeEnum
    (m.edges.items.map .lift ++ m.edges.items.map .enter ++ m.edges.items.map .trExit ++
      m.edges.items.map .trDec ++ m.edges.items.map .trInc ++
      (lives m).flatMap (fun q => (fins _).map (.aInc q)) ++
      (lives m).flatMap (fun q => (fins _).map (.bStep q)) ++
      (lives m).map .bLast ++ (lives m).map .topExit ++ (lives m).map .topDec ++
      (lives m).map .preGo)
    (by
      intro i
      cases i <;> simp [m.edges.complete, mem_lives, mem_fins])
  instruction := move m fresh
  entry := .base m.entry
  halt := .base m.halt

@[simp] theorem rev_instruction (fresh) : (rev m fresh).instruction = move m fresh := rfl
@[simp] theorem rev_entry (fresh) : (rev m fresh).entry = .base (Q:=Q) (P:=Live m) (E:=E) m.entry := rfl
@[simp] theorem rev_halt (fresh) : (rev m fresh).halt = .base (Q:=Q) (P:=Live m) (E:=E) m.halt := rfl

/-! ## Basic facts about lifted operations -/

theorem ready_lift (op : Op R) (f : File (Slot R)) :
    (liftOp op).ready f = op.ready (proj f) := by
  cases op <;> rfl

theorem proj_act_lift (op : Op R) (f : File (Slot R)) :
    proj ((liftOp op).act f) = op.act (proj f) := by
  cases op <;> funext r <;> simp [liftOp, Op.act, proj, put]

theorem act_lift_hist (op : Op R) (f : File (Slot R)) :
    (liftOp op).act f .hist = f .hist := by
  cases op <;> simp [liftOp, Op.act, put]

theorem act_lift_work (op : Op R) (f : File (Slot R)) :
    (liftOp op).act f .work = f .work := by
  cases op <;> simp [liftOp, Op.act, put]

@[simp] theorem proj_put_hist (f : File (Slot R)) (v : Nat) : proj (put f .hist v) = proj f := by
  funext r; simp [proj, put]

@[simp] theorem proj_put_work (f : File (Slot R)) (v : Nat) : proj (put f .work v) = proj f := by
  funext r; simp [proj, put]

theorem castSucc_ne_last {n : Nat} (k : Fin n) : k.castSucc ≠ Fin.last n :=
  Fin.ne_of_lt k.castSucc_lt_last

theorem last_ne_castSucc {n : Nat} (k : Fin n) : Fin.last n ≠ k.castSucc :=
  fun h => castSucc_ne_last k h.symm

theorem idx_inj {e e' : E} (h : idx m e = idx m e') : e = e' :=
  pos_inj (m.edges.complete e) (m.edges.complete e') (congrArg Fin.val h)

@[simp] theorem idx_inj_iff {e e' : E} : idx m e = idx m e' ↔ e = e' :=
  ⟨idx_inj m, fun h => h ▸ rfl⟩

theorem zero_ne_succ {n : Nat} (k : Fin n) : (0 : Fin (n+1)) ≠ k.succ :=
  fun h => Fin.succ_ne_zero k h.symm

/-! ## Reversibility -/

variable {m}

theorem rev_reversible (std : Standard m) : Reversible (rev m std.fresh) := by
  constructor
  · intro i
    cases i <;> simp [move]
    rename_i q
    exact q.property
  · intro i
    cases i <;> simp [move]
    exact std.terminal _
  · rintro ⟨pc, f⟩ i j hi hj
    obtain ⟨h1, hi⟩ := hi
    obtain ⟨h2, hj⟩ := hj
    simp only [rev_instruction] at h1 h2 hi hj ⊢
    subst h1
    cases i <;> cases j <;> simp only [move, ready_lift] at h2 hi hj ⊢
    case lift.lift e e' =>
      congr 1
      exact std.deterministic ⟨(m.instruction e).src, proj f⟩ _ _ ⟨rfl, hi⟩
        ⟨Node.base.inj h2, hj⟩
    all_goals simp [Op.ready, castSucc_ne_last, last_ne_castSucc, Fin.castSucc_inj] at h2 hi hj ⊢
    all_goals simp_all
  · rintro ⟨pc, f⟩ i j hi hj
    obtain ⟨h1, hi⟩ := hi
    obtain ⟨h2, hj⟩ := hj
    simp only [rev_instruction, Edge.inverse] at h1 h2 hi hj ⊢
    subst h1
    cases i <;> cases j <;> simp [move, Op.inv, Op.ready, Fin.succ_inj, zero_ne_succ, Fin.succ_ne_zero, Subtype.ext_iff] at h2 hi hj ⊢
    all_goals simp_all

/-! ## Liveness -/

def liftInput (input : File R) : File (Slot R)
  | .orig r => input r
  | _ => 0

theorem proj_liftInput (input : File R) : proj (liftInput input) = input := rfl

/-- The run invariant: `work` is clear between steps, and `hist` is positive
wherever a lone positivity test is about to be executed. -/
def Good (m : Machine Q R E) : Config (RNode m) (Slot R) → Prop
  | ⟨.base _, f⟩ => f .work = 0
  | ⟨.mid _, f⟩ => f .work = 0
  | ⟨.b _ _, f⟩ => 0 < f .hist
  | ⟨.top _, f⟩ => 0 < f .hist
  | ⟨.pre _, f⟩ => 0 < f .hist
  | _ => True

theorem good_step (std : Standard m) (c : Config (RNode m) (Slot R)) (i : RMove m)
    (hc : Good m c) (h : ((rev m std.fresh).instruction i).enabled c) :
    Good m (((rev m std.fresh).instruction i).target c) := by
  obtain ⟨pc, f⟩ := c
  obtain ⟨h1, h2⟩ := h
  simp only [rev_instruction] at h1 h2 ⊢
  subst h1
  cases i
  case lift e =>
    simp only [move, Edge.target, Good] at hc ⊢
    rw [act_lift_work]; exact hc
  all_goals simp [move, Edge.target, Good, Op.act, Op.ready, put] at hc h2 ⊢
  all_goals omega

theorem good_live (std : Standard m) (c : Config (RNode m) (Slot R)) (hc : Good m c)
    (hn : c.pc ≠ (rev m std.fresh).halt) :
    ∃ i, ((rev m std.fresh).instruction i).enabled c := by
  obtain ⟨pc, f⟩ := c
  simp only [rev_instruction, rev_halt] at hn ⊢
  cases pc with
  | base q =>
    have hq : q ≠ m.halt := fun h => hn (h ▸ rfl)
    obtain ⟨e, he⟩ := std.total ⟨q, proj f⟩ hq
    exact ⟨.lift e, by simp only [move]; exact congrArg Node.base he.1, by simpa [move, ready_lift] using he.2⟩
  | mid e => exact ⟨.enter e, rfl, by simpa [move, Op.ready, Good] using hc⟩
  | tr e =>
    by_cases z : f .hist = 0
    · exact ⟨.trExit e, rfl, by simp [move, Op.ready, z]⟩
    · exact ⟨.trDec e, rfl, by simp [move, Op.ready, z]⟩
  | trInc e => exact ⟨.trInc e, rfl, rfl⟩
  | a q k => exact ⟨.aInc q k, rfl, rfl⟩
  | b q k =>
    have pos : f .hist ≠ 0 := by simp [Good] at hc; omega
    by_cases hk : k.val < width m
    · refine ⟨.bStep q ⟨k.val, hk⟩, ?_, by simp [move, Op.ready, pos]⟩
      simp only [move]; congr
    · refine ⟨.bLast q, ?_, by simp [move, Op.ready, pos]⟩
      simp only [move]; congr; ext; simp; omega
  | top q =>
    by_cases z : f .work = 0
    · exact ⟨.topExit q, rfl, by simp [move, Op.ready, z]⟩
    · exact ⟨.topDec q, rfl, by simp [move, Op.ready, z]⟩
  | pre q =>
    have pos : f .hist ≠ 0 := by simp [Good] at hc; omega
    exact ⟨.preGo q, rfl, by simp [move, Op.ready, pos]⟩

theorem rev_live (std : Standard m) (input : File R) :
    (rev m std.fresh).live (liftInput input) := by
  intro n hn
  exact good_live std _
    (path_invariant (rev m std.fresh) (liftInput input) (Good m) rfl (good_step std) n) hn

/-! ## The reversible run reaches halt exactly when the source does -/

/-- The source configuration that a reversible configuration is working on. -/
def assoc (m : Machine Q R E) : Config (RNode m) (Slot R) → Config Q R
  | ⟨.base q, f⟩ => ⟨q, proj f⟩
  | ⟨.mid e, f⟩ => ⟨(m.instruction e).dest, proj f⟩
  | ⟨.tr e, f⟩ => ⟨(m.instruction e).dest, proj f⟩
  | ⟨.trInc e, f⟩ => ⟨(m.instruction e).dest, proj f⟩
  | ⟨.a q _, f⟩ => ⟨q.val, proj f⟩
  | ⟨.b q _, f⟩ => ⟨q.val, proj f⟩
  | ⟨.top q, f⟩ => ⟨q.val, proj f⟩
  | ⟨.pre q, f⟩ => ⟨q.val, proj f⟩

theorem track_step (std : Standard m) (input : File R) (c : Config (RNode m) (Slot R))
    (i : RMove m) (hc : ∃ n, assoc m c = m.path input n)
    (h : ((rev m std.fresh).instruction i).enabled c) :
    ∃ n, assoc m (((rev m std.fresh).instruction i).target c) = m.path input n := by
  obtain ⟨pc, f⟩ := c
  obtain ⟨h1, h2⟩ := h
  obtain ⟨n, hn⟩ := hc
  simp only [rev_instruction] at h1 h2 ⊢
  subst h1
  cases i
  case lift e =>
    refine ⟨n+1, ?_⟩
    simp only [move, ready_lift] at h2
    simp only [move, assoc] at hn
    have go : (m.instruction e).enabled (m.path input n) := by
      rw [← hn]; exact ⟨rfl, h2⟩
    rw [path_succ std.deterministic go, ← hn]
    simp [move, Edge.target, assoc, proj_act_lift]
  all_goals exact ⟨n, by simpa [move, Edge.target, assoc, Op.act] using hn⟩

theorem halt_of_rev (std : Standard m) (input : File R)
    (h : ∃ s, ((rev m std.fresh).path (liftInput input) s).pc = (rev m std.fresh).halt) :
    ∃ n, (m.path input n).pc = m.halt := by
  obtain ⟨s, hs⟩ := h
  have inv := path_invariant (rev m std.fresh) (liftInput input)
    (fun c => ∃ n, assoc m c = m.path input n) ⟨0, rfl⟩
    (fun c i hc h => track_step std input c i hc h)
  obtain ⟨n, hn⟩ := inv s
  generalize (rev m std.fresh).path (liftInput input) s = c at hs hn
  obtain ⟨pc, f⟩ := c
  simp only [rev_halt] at hs
  subst hs
  exact ⟨n, by rw [← hn]; rfl⟩

def Reach (std : Standard m) (c d : Config (RNode m) (Slot R)) : Prop :=
  ∃ s, iterate (fun c => ((rev m std.fresh).next c).getD c) c s = d

theorem reach_refl (std : Standard m) (c : Config (RNode m) (Slot R)) : Reach std c c := ⟨0, rfl⟩

theorem reach_trans {std : Standard m} {c d e : Config (RNode m) (Slot R)}
    (h1 : Reach std c d) (h2 : Reach std d e) : Reach std c e := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  exact ⟨s+t, by rw [iterate_add, hs, ht]⟩

theorem reach_edge {std : Standard m} {c d : Config (RNode m) (Slot R)} (i : RMove m)
    (h : ((rev m std.fresh).instruction i).enabled c)
    (hd : ((rev m std.fresh).instruction i).target c = d) : Reach std c d :=
  ⟨1, by
    show ((rev m std.fresh).next c).getD c = d
    rw [next_of_enabled (rev_reversible std).deterministic h, ← hd]; rfl⟩

theorem transfer (std : Standard m) (e : E) :
    ∀ n (f : File (Slot R)), f .hist = n →
      ∃ g, Reach std ⟨.tr e, f⟩ ⟨.tr e, g⟩ ∧ g .hist = 0 ∧ proj g = proj f := by
  intro n
  induction n with
  | zero => intro f h; exact ⟨f, reach_refl std _, h, rfl⟩
  | succ n ih =>
    intro f h
    let f1 := put f .hist (f .hist - 1)
    let f2 := put f1 .work (f1 .work + 1)
    obtain ⟨g, hr, hg, hp⟩ := ih f2 (by simp [f2, f1, put, h])
    refine ⟨g, reach_trans (reach_edge (.trDec e) ⟨rfl, ?_⟩ rfl)
      (reach_trans (reach_edge (.trInc e) ⟨rfl, rfl⟩ rfl) hr), hg, ?_⟩
    · simp [move, Op.ready, h]
    · rw [hp]; simp [f2, f1]

theorem chain (std : Standard m) (q : Live m) :
    ∀ d (k : Fin (width m + 1)) (f : File (Slot R)), width m - k.val = d →
      ∃ g, Reach std ⟨.a q k, f⟩ ⟨.top q, g⟩ ∧ 0 < g .hist ∧ g .work = f .work ∧
        proj g = proj f := by
  intro d
  induction d with
  | zero =>
    intro k f hd
    have hk : k = Fin.last _ := Fin.ext (by simp; omega)
    subst hk
    let f1 := put f .hist (f .hist + 1)
    refine ⟨f1, reach_trans (reach_edge (.aInc q (Fin.last _)) ⟨rfl, rfl⟩ rfl)
      (reach_edge (.bLast q) ⟨rfl, ?_⟩ rfl), ?_, ?_, ?_⟩
    · simp [move, Edge.target, Op.act, Op.ready, put]
    all_goals simp [f1, put]
  | succ d ih =>
    intro k f hd
    have hk : k.val < width m := by omega
    let k' : Fin (width m) := ⟨k.val, hk⟩
    have kk : k = k'.castSucc := rfl
    let f1 := put f .hist (f .hist + 1)
    obtain ⟨g, hr, hg, hw, hp⟩ := ih k'.succ f1 (by simp [k']; omega)
    refine ⟨g, reach_trans (reach_edge (.aInc q k) ⟨rfl, rfl⟩ rfl)
      (reach_trans (reach_edge (.bStep q k') ⟨by rw [kk]; rfl, ?_⟩ rfl) hr), hg, ?_, ?_⟩
    · simp [move, Edge.target, Op.act, Op.ready, put]
    · rw [hw]; simp [f1, put]
    · rw [hp]; simp [f1]

theorem loop (std : Standard m) (q : Live m) :
    ∀ w (f : File (Slot R)), f .work = w → 0 < f .hist →
      ∃ g, Reach std ⟨.top q, f⟩ ⟨.top q, g⟩ ∧ g .work = 0 ∧ proj g = proj f := by
  intro w
  induction w with
  | zero => intro f h _; exact ⟨f, reach_refl std _, h, rfl⟩
  | succ w ih =>
    intro f h pos
    let f1 := put f .work (f .work - 1)
    obtain ⟨g1, r1, p1, w1, j1⟩ := chain std q _ 0 f1 rfl
    obtain ⟨g, r2, w2, j2⟩ := ih g1 (by rw [w1]; simp [f1, put, h]) p1
    refine ⟨g, reach_trans (reach_edge (.topDec q) ⟨rfl, ?_⟩ rfl)
      (reach_trans (reach_edge (.preGo q) ⟨rfl, ?_⟩ rfl) (reach_trans r1 r2)), w2, ?_⟩
    · simp [move, Op.ready, h]
    · simp [move, Edge.target, Op.act, Op.ready, put]; omega
    · rw [j2, j1]; simp [f1]

theorem segment (std : Standard m) {f : File (Slot R)} {e : E} (hw : f .work = 0)
    (hen : (m.instruction e).op.ready (proj f) = true) :
    ∃ g, Reach std ⟨.base (m.instruction e).src, f⟩ ⟨.base (m.instruction e).dest, g⟩ ∧
      g .work = 0 ∧ proj g = (m.instruction e).op.act (proj f) := by
  let f1 := (liftOp (m.instruction e).op).act f
  obtain ⟨g2, r2, h2, p2⟩ := transfer std e _ f1 rfl
  let t : Live m := ⟨(m.instruction e).dest, std.fresh e⟩
  obtain ⟨g3, r3, h3, _, p3⟩ := chain std t _ (idx m e) g2 rfl
  obtain ⟨g4, r4, w4, p4⟩ := loop std t _ g3 rfl h3
  refine ⟨g4, ?_, w4, ?_⟩
  · refine reach_trans (reach_edge (.lift e) ⟨rfl, ?_⟩ rfl) ?_
    · simpa [move, ready_lift] using hen
    refine reach_trans (reach_edge (.enter e) ⟨rfl, ?_⟩ rfl) ?_
    · simp [move, Edge.target, Op.ready, act_lift_work, hw]
    refine reach_trans r2 (reach_trans (reach_edge (.trExit e) ⟨rfl, ?_⟩ rfl) ?_)
    · simp [move, Op.ready, h2]
    refine reach_trans r3 (reach_trans r4 (reach_edge (.topExit t) ⟨rfl, ?_⟩ rfl))
    simp [move, Op.ready, w4]
  · rw [p4, p3, p2]; simp [f1, proj_act_lift]

theorem rev_of_halt (std : Standard m) (input : File R)
    (h : ∃ n, (m.path input n).pc = m.halt) :
    ∃ s, ((rev m std.fresh).path (liftInput input) s).pc = (rev m std.fresh).halt := by
  have claim : ∀ n, ∃ j g, Reach std ⟨.base m.entry, liftInput input⟩
      ⟨.base (m.path input j).pc, g⟩ ∧ g .work = 0 ∧ proj g = (m.path input j).data ∧
      (j = n ∨ (m.path input j).pc = m.halt) := by
    intro n
    induction n with
    | zero => exact ⟨0, liftInput input, reach_refl std _, rfl, rfl, Or.inl rfl⟩
    | succ n ih =>
      obtain ⟨j, g, hr, hw, hp, hj⟩ := ih
      by_cases hh : (m.path input j).pc = m.halt
      · exact ⟨j, g, hr, hw, hp, Or.inr hh⟩
      have jn : j = n := hj.resolve_right hh
      obtain ⟨e, he⟩ := std.total (m.path input j) hh
      obtain ⟨g', hr', hw', hp'⟩ := segment std hw (e := e) (hp ▸ he.2)
      refine ⟨j+1, g', ?_, hw', ?_, Or.inl (by omega)⟩
      · rw [path_succ std.deterministic he]
        exact reach_trans hr (he.1 ▸ hr')
      · rw [path_succ std.deterministic he, hp']; simp [Edge.target, hp]
  obtain ⟨N, hN⟩ := h
  obtain ⟨j, g, ⟨s, hs⟩, _, _, hj⟩ := claim N
  have hh : (m.path input j).pc = m.halt := hj.elim (fun e => e ▸ hN) id
  refine ⟨s, ?_⟩
  have run : (rev m std.fresh).path (liftInput input) s = ⟨.base (m.path input j).pc, g⟩ := hs
  rw [run, hh]; rfl

/-! ## The end-to-end theorem -/

/-- Every standard deterministic counter machine reduces to exact repetition of
the six-symbol tag system. The source machine need not be reversible, and no
run-time liveness assumption remains. -/
theorem halt_iff_exact_cycle (m : Machine Q R E) (std : Standard m) (input : File R) :
    (∃ n, (m.path input n).pc = m.halt) ↔
      ExactCycle (encode (rev m std.fresh) (liftInput input)) := by
  rw [← SixSymbol.halt_iff_exact_cycle _ _ (rev_reversible std) (rev_live std input)]
  exact ⟨rev_of_halt std input, halt_of_rev std input⟩

#print axioms halt_iff_exact_cycle

/-! ## An irreversible example

This machine empties its register and halts. Its countdown loop merges many
configurations into one, so it is not reversible, yet it is `Standard`. -/

namespace Example

inductive State where | entry | count | halt
  deriving DecidableEq, Repr

inductive Label where | start | done | down
  deriving DecidableEq, Repr

def machine : Machine State Unit Label where
  states := ⟨[.entry, .count, .halt], by decide, by intro i; cases i <;> decide⟩
  regs := ⟨[()], by decide, by intro i; cases i; decide⟩
  edges := ⟨[.start, .done, .down], by decide, by intro i; cases i <;> decide⟩
  instruction
    | .start => ⟨.entry, .nop, .count⟩
    | .done => ⟨.count, .testZ (), .halt⟩
    | .down => ⟨.count, .dec (), .count⟩
  entry := .entry
  halt := .halt

theorem standard : Standard machine := by
  constructor
  · intro i; cases i <;> decide
  · intro i; cases i <;> decide
  · rintro ⟨pc, x⟩ i j hi hj
    cases i <;> cases j <;> simp_all [Edge.enabled, machine, Op.ready]
  · rintro ⟨pc, x⟩ hpc
    cases pc with
    | entry => exact ⟨.start, rfl, rfl⟩
    | count =>
      by_cases z : x () = 0
      · exact ⟨.done, rfl, by simp [machine, Op.ready, z]⟩
      · exact ⟨.down, rfl, by simp [machine, Op.ready, z]⟩
    | halt => exact absurd rfl hpc

theorem not_reversible : ¬ Reversible machine := by
  intro rev
  have := rev.backward ⟨.count, fun _ => 0⟩ .start .down
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  cases this

theorem halts_on_three : ExactCycle (encode (rev machine standard.fresh) (liftInput (fun _ => 3))) :=
  (halt_iff_exact_cycle machine standard _).mp ⟨5, rfl⟩

end Example

end ReversibleCounter
