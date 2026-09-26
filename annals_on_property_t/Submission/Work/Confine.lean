import Submission.Work.CancelPair
import Submission.Work.AggregateT1

open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# Confined fully-cancelled factors (the T1 aggregate core, selection proved)

Machine-validated combinatorial core of the general-`k` aggregate lemma T1
(see `AggregateT1.lean`): for a concatenation `W = L₀ ++ ⋯ ++ L_{k-1}` of
reduced words whose reduction has at most one letter, there is a **confined
fully-cancelled factor**: a factor whose block contains no survivor letter
and whose every letter is cancelled against a letter of an *adjacent* block
only.

## The selection rule (validated exhaustively)

`cancelledPairs` (see `CancelPair.lean`) is a non-crossing matching of all
non-survivor positions.  Call a pair `(i,j)` (`i < j`) a **jump** when its
endpoints lie in blocks at distance ≥ 2 (`l ≥ t + 2`, `i ∈ B_t`, `j ∈ B_l`).
Machine validation: exhaustive n = 2, factor length ≤ 3, k = 2..5 (1 301 284
instances with ≤ 1 survivor) and all non-crossing perfect matchings on ≤ 10
points (1502 configs): **0 failures** for the rule:

* if a jump exists, take one of *minimal length* `j - i`; if its left
  endpoint lies in block `t`, then block `t+1` is confined and fully
  cancelled;
* if no jump exists, every block is confined (all partners are in adjacent
  blocks), and any block avoiding the survivor works.

## Why the minimal jump gives a confined block (proof sketch)

Let `(i, j)` be a minimal-length jump with `i ∈ B_t`, `j ∈ B_l`, `l ≥ t+2`.
Every point strictly between `i` and `j` pairs within `(i, j)`
(`pair_interval_complete`), and a survivor cannot lie strictly inside a pair
(`survivor_not_inside_pair`).  Hence `B_{t+1} ⊆ (i,j)` contains no survivor
and every letter `p ∈ B_{t+1}` has its partner `y` strictly inside `(i,j)`.
`y ∉ B_{t+1}` (a pair never lies inside a reduced factor:
`pair_not_in_reduced_factor`).  If `y < p` then `y ∈ B_t` (adjacent); if
`y > p` and `y ∈ B_{t'}` with `t' ≥ t+3`, then `(p, y)` is a jump strictly
inside `(i,j)`, of smaller length — contradicting minimality.  So `y` lies in
`B_t ∪ B_{t+2}`: adjacent to `B_{t+1}`, i.e. `B_{t+1}` is confined.

This file builds that proof: positional block bookkeeping for a list of
factors, the jump relation, confinement, and the main existence theorem
`confined_factor_exists`.  All lemmas kernel-checked; axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## Block arithmetic for a list of factors -/

variable {α : Type*}

/-- Block start of the `j`-th factor in a list of factors: the position in
`Fs.flatten` where factor `j` begins (`0` outside the range). -/
def BlockStart : List (List α) → ℕ → ℕ
  | [], _ => 0
  | _ :: _, 0 => 0
  | f :: t, j + 1 => f.length + BlockStart t j

/-- The position `p` of `Fs.flatten` lies in the (in-range) block of the
`j`-th factor. -/
def InBlock (Fs : List (List α)) (j p : ℕ) : Prop :=
  j < Fs.length ∧ BlockStart Fs j ≤ p ∧ p < BlockStart Fs (j + 1)

/-- Blocks `j` and `j'` are neighbours in the chain of factors. -/
def AdjacentBlock (j j' : ℕ) : Prop := j' = j + 1 ∨ j = j' + 1

/-- A factor block contains no survivor position of the joined word. -/
def FullyCancelled {α : Type*} [DecidableEq α] (Fs : List (List (α × Bool)))
    (j : ℕ) : Prop :=
  ∀ p : ℕ, InBlock Fs j p → p ∉ survivorPos Fs.flatten

/-- A factor is *confined*: its block is fully cancelled and every partner of
every one of its letters lies in an adjacent block. -/
def Confined {α : Type*} [DecidableEq α] (Fs : List (List (α × Bool)))
    (j : ℕ) : Prop :=
  FullyCancelled Fs j ∧
    ∀ p : ℕ, InBlock Fs j p → ∀ y : ℕ,
      (p, y) ∈ cancelledPairs Fs.flatten ∨ (y, p) ∈ cancelledPairs Fs.flatten →
        ∃ j' : ℕ, AdjacentBlock j j' ∧ InBlock Fs j' y

/-- A cancelled pair `(i, j)` (with `i` in block `t`, `j` in block `l`) is a
*jump* across at least one whole block (`l ≥ t+2`). -/
def IsJump {α : Type*} [DecidableEq α] (Fs : List (List (α × Bool)))
    (i j : ℕ) : Prop :=
  ∃ t l : ℕ, InBlock Fs t i ∧ InBlock Fs l j ∧ l ≥ t + 2 ∧
    (i, j) ∈ cancelledPairs Fs.flatten

/-- No cancelled pair jumps over a whole block. -/
def JumpFree {α : Type*} [DecidableEq α] (Fs : List (List (α × Bool))) : Prop :=
  ∀ i j t l : ℕ, InBlock Fs t i → InBlock Fs l j →
    (i, j) ∈ cancelledPairs Fs.flatten → ¬ l ≥ t + 2

@[simp] lemma BlockStart_nil (j : ℕ) : BlockStart ([] : List (List α)) j = 0 := by
  cases j <;> rfl

@[simp] lemma BlockStart_cons_zero (f : List α) (t : List (List α)) :
    BlockStart (f :: t) 0 = 0 := rfl

@[simp] lemma BlockStart_cons_succ (f : List α) (t : List (List α)) (j : ℕ) :
    BlockStart (f :: t) (j + 1) = f.length + BlockStart t j := rfl

/-- The block start is monotone in the block index. -/
lemma BlockStart_mono (Fs : List (List α)) {j j' : ℕ} (hjj : j ≤ j') :
    BlockStart Fs j ≤ BlockStart Fs j' := by
  induction Fs generalizing j j' with
  | nil => simp
  | cons f t ih =>
      cases j with
      | zero => simp
      | succ j =>
          cases j' with
          | zero => omega
          | succ j' =>
              simp
              exact ih (by omega)

/-- For an index beyond the list length the block start is the total length. -/
lemma BlockStart_eq_length (Fs : List (List α)) {j : ℕ} (hj : Fs.length ≤ j) :
    BlockStart Fs j = Fs.flatten.length := by
  induction Fs generalizing j with
  | nil => simp
  | cons f t ih =>
      cases j with
      | zero => simp at hj
      | succ j =>
          have hj' : t.length ≤ j := by simpa using (Nat.succ_le_succ_iff.mp hj)
          simp [ih hj']

/-- The block start of the successor is the block start plus the length of
the `j`-th factor (valid in range). -/
lemma BlockStart_succ_in (Fs : List (List α)) {j : ℕ} (hj : j < Fs.length) :
    BlockStart Fs (j + 1) = BlockStart Fs j + Fs[j].length := by
  induction Fs generalizing j with
  | nil => simp at hj
  | cons f t ih =>
      cases j with
      | zero =>
          cases t with
          | nil => simp [BlockStart]
          | cons g u => simp [BlockStart]
      | succ j0 =>
          have hj0 : j0 < t.length := by simpa using hj
          have hge : (f :: t)[j0 + 1] = t[j0] := rfl
          calc
            BlockStart (f :: t) (j0 + 2) = f.length + BlockStart t (j0 + 1) := by rfl
            _ = f.length + (BlockStart t j0 + t[j0].length) := by rw [ih hj0]
            _ = (f.length + BlockStart t j0) + t[j0].length := by omega
            _ = BlockStart (f :: t) (j0 + 1) + (f :: t)[j0 + 1].length := by
              rw [hge]
              simp [BlockStart]

/-- In-range block starts are strictly increasing: block `j` ends where block
`j+1` starts, and nonempty factors make the start strictly grow. -/
lemma InBlock_start_lt_next {Fs : List (List α)} {j : ℕ} (hj : j + 1 < Fs.length)
    {f : List α} (hf : Fs[j + 1] ≠ []) :
    BlockStart Fs (j + 1) < BlockStart Fs (j + 2) := by
  have hbj : j + 1 < Fs.length := hj
  have hnon : 0 < Fs[j + 1].length := by
    exact Nat.pos_of_ne_zero (by intro h; apply hf; exact (List.eq_nil_iff_length_eq_zero.mpr h))
  have hsucc := BlockStart_succ_in Fs (j := j + 1) hbj
  rw [hsucc]
  omega

/-! ## Positions and blocks -/

/-- A position in the `j`-th block equals the block start plus an offset
below the block length. -/
lemma InBlock_iff_offset {Fs : List (List α)} {j p : ℕ} (hj : j < Fs.length) :
    InBlock Fs j p ↔ ∃ r : ℕ, r < Fs[j].length ∧ p = BlockStart Fs j + r := by
  constructor
  · intro h
    rcases h with ⟨hj, hle, hlt⟩
    refine ⟨p - BlockStart Fs j, ?_, by omega⟩
    have hsucc := BlockStart_succ_in Fs hj
    have hlt' : p < BlockStart Fs j + Fs[j].length := by rwa [hsucc] at hlt
    omega
  · rintro ⟨r, hr, hp⟩
    subst p
    refine ⟨hj, ?_, ?_⟩
    · omega
    · have hsucc := BlockStart_succ_in Fs hj
      rw [hsucc]
      omega

/-- If a position lies in block `j` then it is below the total length. -/
lemma InBlock_lt_total {Fs : List (List α)} {j p : ℕ} (h : InBlock Fs j p) :
    p < Fs.flatten.length := by
  rcases h with ⟨hj, hle, hlt⟩
  have htot := BlockStart_eq_length Fs (j := Fs.length) (by omega)
  have hmono : BlockStart Fs (j + 1) ≤ BlockStart Fs Fs.length := by
    exact BlockStart_mono Fs (by omega)
  omega

/-- Every position below the total length lies in some block. -/
lemma exists_InBlock {Fs : List (List α)} {p : ℕ} (hp : p < Fs.flatten.length) :
    ∃ j : ℕ, InBlock Fs j p := by
  induction Fs generalizing p with
  | nil => simp at hp
  | cons f t ih =>
      by_cases hpf : p < f.length
      · refine ⟨0, ?_⟩
        simp [InBlock]
        omega
      · have hrest : p - f.length < t.flatten.length := by
          have : (f :: t).flatten.length = f.length + t.flatten.length := by simp
          omega
        rcases ih hrest with ⟨j, hj⟩
        refine ⟨j + 1, ?_⟩
        rcases hj with ⟨hjl, hle, hlt⟩
        simp [InBlock]
        refine ⟨by simpa, ?_, ?_⟩
        · have hle' : f.length + BlockStart t j ≤ p := by omega
          simpa using hle'
        · have hlt' : p < f.length + BlockStart t (j + 1) := by omega
          simpa using hlt'

lemma InBlock_lt_of_lt {Fs : List (List α)} {j j' p : ℕ}
    (h : InBlock Fs j p) (hlt : j < j') : p < BlockStart Fs j' := by
  have hmono1 : BlockStart Fs (j + 1) ≤ BlockStart Fs j' := BlockStart_mono Fs (by omega)
  rcases h with ⟨hj, hle, hlt1⟩
  have : p < BlockStart Fs (j + 1) := hlt1
  omega

/-- The block of a position is unique. -/
lemma InBlock_unique {Fs : List (List α)} {j j' p : ℕ}
    (h : InBlock Fs j p) (h' : InBlock Fs j' p) : j = j' := by
  by_cases hlt : j < j'
  · have hbad := InBlock_lt_of_lt h hlt
    rcases h' with ⟨_, hle', hlt'⟩
    omega
  · have hle : j' ≤ j := le_of_not_gt hlt
    rcases lt_or_eq_of_le hle with hlt' | hEq
    · have hbad := InBlock_lt_of_lt h' hlt'
      rcases h with ⟨_, hle, hlt1⟩
      omega
    · exact hEq.symm


/-! ## Factor decomposition of the joined word -/

/-- Flattening a cons appends the head factor. -/
@[simp] lemma flatten_cons (f : List α) (t : List (List α)) :
    (f :: t).flatten = f ++ t.flatten := rfl

/-- The block start equals the length of the flattened prefix. -/
lemma BlockStart_eq_take (Fs : List (List α)) (j : ℕ) :
    BlockStart Fs j = (Fs.take j).flatten.length := by
  induction Fs generalizing j with
  | nil => simp
  | cons f t ih =>
      cases j with
      | zero => simp
      | succ j =>
          have hih := ih j
          simp [hih]

/-- The total length is the block start at the list length. -/
lemma BlockStart_length (Fs : List (List α)) :
    BlockStart Fs Fs.length = Fs.flatten.length := by
  rw [BlockStart_eq_take]
  simp

/-- Flattening is the concatenation: prefix, `j`-th factor, suffix. -/
lemma flatten_middle (Fs : List (List α)) {j : ℕ} (hj : j < Fs.length) :
    Fs.flatten = (Fs.take j).flatten ++ Fs[j] ++ (Fs.drop (j + 1)).flatten := by
  induction Fs generalizing j with
  | nil => simp at hj
  | cons f t ih =>
      cases j with
      | zero =>
          simp
      | succ j0 =>
          have hj0 : j0 < t.length := by simpa using hj
          have hge : (f :: t)[j0 + 1] = t[j0] := rfl
          have hih := ih hj0
          simp [hge]
          rw [hih]
          -- (f::t).drop (j0+2) = t.drop (j0+1): checked by simp above? final assemble
          simp [List.append_assoc]

/-- An internal pair cannot lie inside a single reduced factor block. -/
lemma no_pair_inside_block {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {x y j : ℕ} (hp : (x, y) ∈ cancelledPairs Fs.flatten)
    (hx : InBlock Fs j x) (hy : InBlock Fs j y) : False := by
  have hj : j < Fs.length := hx.1
  have hxy : x < y := pair_lt Fs.flatten hp
  let A : List (α × Bool) := (Fs.take j).flatten
  let F : List (α × Bool) := Fs[j]
  let B : List (α × Bool) := (Fs.drop (j + 1)).flatten
  have hsplit : Fs.flatten = A ++ F ++ B := by
    simpa [A, F, B] using flatten_middle Fs hj
  have hA : A.length = BlockStart Fs j := by
    change (Fs.take j).flatten.length = BlockStart Fs j
    exact (BlockStart_eq_take Fs j).symm
  have hFlen : F.length = Fs[j].length := rfl
  have hAx : A.length ≤ x := by
    rw [hA]
    exact hx.2.1
  have hyB : y < A.length + F.length := by
    have hsucc : BlockStart Fs (j + 1) = BlockStart Fs j + Fs[j].length :=
      BlockStart_succ_in Fs hj
    rw [hA, hFlen, ← hsucc]
    exact hy.2.2
  have hF : FreeGroup.IsReduced F := by
    have hmem : Fs[j] ∈ Fs := List.getElem_mem hj
    simpa [F] using hred (Fs[j]) hmem
  have hp' : (x, y) ∈ cancelledPairs (A ++ F ++ B) := by
    simpa [hsplit] using hp
  exact pair_not_in_reduced_factor A F B hF hp' hAx hyB

/-- Endpoints of a cancelled pair of the joined word lie below its length. -/
lemma pair_pos_lt {α : Type*} [DecidableEq α] (Fs : List (List (α × Bool)))
    {i j : ℕ} (hp : (i, j) ∈ cancelledPairs Fs.flatten) :
    i < Fs.flatten.length ∧ j < Fs.flatten.length := by
  have hj := pair_lt_length Fs.flatten hp
  have hi := pair_lt Fs.flatten hp
  exact ⟨lt_trans hi hj, hj⟩

/-! ## The partner of a letter strictly inside a pair stays inside -/

/-- A letter strictly inside a cancelled pair is paired with a letter
strictly inside the same pair (`pair_interval_complete` + partner
uniqueness). -/
lemma partner_inside_pair {α : Type*} [DecidableEq α] (W : List (α × Bool))
    {i j p y : ℕ} (hp : (i, j) ∈ cancelledPairs W) (hpi : i < p) (hpj : p < j)
    (hpy : (p, y) ∈ cancelledPairs W ∨ (y, p) ∈ cancelledPairs W) :
    i < y ∧ y < j := by
  rcases pair_interval_complete W hp p hpi hpj with ⟨y0, hiy0, hy0j, hy0p⟩
  rcases hpy with hpy1 | hpy2
  · rcases hy0p with hy0p1 | hy0p2
    · have heq := pair_eq_of_share W hpy1 hy0p1 (Or.inl rfl)
      have hy : y = y0 := congrArg Prod.snd heq
      subst y
      exact ⟨hiy0, hy0j⟩
    · have heq := pair_eq_of_share W hpy1 hy0p2 (Or.inr (Or.inl rfl))
      have hy : y = p := congrArg Prod.snd heq
      have hlt := pair_lt W hpy1
      omega
  · rcases hy0p with hy0p1 | hy0p2
    · have heq := pair_eq_of_share W hpy2 hy0p1 (Or.inr (Or.inr (Or.inl rfl)))
      have hy : y = p := congrArg Prod.fst heq
      have hlt := pair_lt W hpy2
      omega
    · have heq := pair_eq_of_share W hpy2 hy0p2 (Or.inr (Or.inr (Or.inr rfl)))
      have hy : y = y0 := congrArg Prod.fst heq
      subst y
      exact ⟨hiy0, hy0j⟩

/-- A survivor never lies strictly inside a pair. -/
lemma survivor_not_strictly_inside {α : Type*} [DecidableEq α]
    (W : List (α × Bool)) {i j p : ℕ} (hp : (i, j) ∈ cancelledPairs W)
    (hsur : p ∈ survivorPos W) : ¬ (i < p ∧ p < j) :=
  survivor_not_inside_pair W hp hsur

/-! ## The jump confinement theorem -/

/-- Every position of the block right after the left endpoint of a minimal
jump is strictly inside the jump pair. -/
lemma jump_inside {Fs : List (List α)} {i j t l : ℕ}
    (hi : InBlock Fs t i) (hl : InBlock Fs l j) (hlt : l ≥ t + 2) {p : ℕ}
    (hp : InBlock Fs (t + 1) p) : i < p ∧ p < j := by
  have hiend : i < BlockStart Fs (t + 1) := hi.2.2
  have hpstart : BlockStart Fs (t + 1) ≤ p := hp.2.1
  have hpend : p < BlockStart Fs (t + 2) := hp.2.2
  have hmono : BlockStart Fs (t + 2) ≤ BlockStart Fs l := BlockStart_mono Fs hlt
  have hjstart : BlockStart Fs l ≤ j := hl.2.1
  constructor
  · omega
  · omega

/-- For a *minimal-length* jump with left endpoint in block `t`, the block
`t+1` is confined and fully cancelled. -/
theorem confined_after_jump {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {i j t l : ℕ} (hi : InBlock Fs t i) (hl : InBlock Fs l j)
    (hlt : l ≥ t + 2) (hp : (i, j) ∈ cancelledPairs Fs.flatten)
    (hmin : ∀ i' j' t' l' : ℕ, InBlock Fs t' i' → InBlock Fs l' j' →
      l' ≥ t' + 2 → (i', j') ∈ cancelledPairs Fs.flatten → j' - i' ≥ j - i) :
    Confined Fs (t + 1) := by
  have htl : t + 1 < Fs.length := by
    have hl' : l < Fs.length := hl.1
    omega
  constructor
  · intro p hp' hsur
    have hins := jump_inside hi hl hlt hp'
    have hbad := survivor_not_inside_pair Fs.flatten hp hsur
    exact hbad hins
  · intro p hp' y hpy
    have hins := jump_inside hi hl hlt hp'
    have hiy : i < y ∧ y < j := partner_inside_pair Fs.flatten hp hins.1 hins.2 hpy
    have hylt : y < Fs.flatten.length := by
      rcases hpy with hpy1 | hpy2
      · exact (pair_pos_lt Fs hpy1).2
      · exact (pair_pos_lt Fs hpy2).1
    rcases exists_InBlock hylt with ⟨t', ht'y⟩
    have hneq : p ≠ y := by
      intro he
      subst p
      rcases hpy with hpy1 | hpy2
      · have hlt := pair_lt Fs.flatten hpy1
        omega
      · have hlt := pair_lt Fs.flatten hpy2
        omega
    have ht'ne : t' ≠ t + 1 := by
      intro he
      subst t'
      rcases hpy with hpy1 | hpy2
      · exact no_pair_inside_block Fs hred hpy1 hp' ht'y
      · exact no_pair_inside_block Fs hred hpy2 ht'y hp'
    by_cases hyp : y < p
    · -- y < p: y's block is t (must be >= t since y > i; and <= t+1 since y < p in t+1; != t+1)
      have htge : t ≤ t' := by
        by_contra h
        have ht'lt : t' < t := lt_of_not_ge h
        have hmono : BlockStart Fs (t' + 1) ≤ BlockStart Fs t := BlockStart_mono Fs (by omega)
        have hy2 : y < BlockStart Fs (t' + 1) := ht'y.2.2
        have hi2 : i ≥ BlockStart Fs t := hi.2.1
        omega
      have ht'le : t' ≤ t + 1 := by
        by_contra h
        have ht'ge : t + 2 ≤ t' := by omega
        have hmono : BlockStart Fs (t + 2) ≤ BlockStart Fs t' := BlockStart_mono Fs ht'ge
        have hp2 : p < BlockStart Fs (t + 2) := hp'.2.2
        have hy3 : BlockStart Fs t' ≤ y := ht'y.2.1
        omega
      have ht' : t' = t := by omega
      refine ⟨t, ?_, ?_⟩
      · right
        omega
      · rwa [← ht']
    · -- y > p
      have hpylt : p < y := by omega
      have ht'ge : t + 1 ≤ t' := by
        by_contra h
        have ht'le : t' ≤ t := by omega
        have hmono : BlockStart Fs (t' + 1) ≤ BlockStart Fs (t + 1) := BlockStart_mono Fs (by omega)
        have hy2 : y < BlockStart Fs (t' + 1) := ht'y.2.2
        have hp2 : p ≥ BlockStart Fs (t + 1) := hp'.2.1
        omega
      have ht'le : t' ≤ t + 2 := by
        by_contra h
        have ht'ge : t + 3 ≤ t' := by omega
        have hpair : (p, y) ∈ cancelledPairs Fs.flatten := by
          rcases hpy with hpy1 | hpy2
          · exact hpy1
          · have hlt2 : y < p := pair_lt Fs.flatten hpy2
            omega
        have hminy := hmin p y (t + 1) t' hp' ht'y (by omega) hpair
        have hlen : y - p < j - i := by omega
        omega
      have ht' : t' = t + 2 := by omega
      refine ⟨t + 2, ?_, ?_⟩
      · left
        omega
      · rwa [← ht']


/-! ## The no-jump case: every fully-cancelled block is confined -/

/-- Block indices are ordered consistently with positions. -/
lemma InBlock_le_of_lt {Fs : List (List α)} {t t' x y : ℕ}
    (hx : InBlock Fs t x) (hy : InBlock Fs t' y) (hxy : x < y) : t ≤ t' := by
  by_contra h
  have ht'lt : t' < t := by omega
  have hmono : BlockStart Fs (t' + 1) ≤ BlockStart Fs t := BlockStart_mono Fs (by omega)
  have hy2 : y < BlockStart Fs (t' + 1) := hy.2.2
  have hx1 : BlockStart Fs t ≤ x := hx.2.1
  omega

/-- Under `JumpFree` a fully-cancelled block is confined (every partner of a
letter of the block lies in an adjacent block). -/
theorem confined_no_jump {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    (hjf : JumpFree Fs) {j : ℕ} (hj : j < Fs.length)
    (hfc : FullyCancelled Fs j) : Confined Fs j := by
  constructor
  · exact hfc
  · intro p hp' y hpy
    have hylt : y < Fs.flatten.length := by
      rcases hpy with hpy1 | hpy2
      · exact (pair_pos_lt Fs hpy1).2
      · exact (pair_pos_lt Fs hpy2).1
    rcases exists_InBlock hylt with ⟨t', ht'y⟩
    have ht'ne : t' ≠ j := by
      intro he
      subst t'
      rcases hpy with hpy1 | hpy2
      · exact no_pair_inside_block Fs hred hpy1 hp' ht'y
      · exact no_pair_inside_block Fs hred hpy2 ht'y hp'
    rcases hpy with hpy1 | hpy2
    · have hpylt : p < y := pair_lt Fs.flatten hpy1
      have hjle : j ≤ t' := InBlock_le_of_lt hp' ht'y hpylt
      have hbad : ¬ t' ≥ j + 2 := hjf p y j t' hp' ht'y hpy1
      have ht'2 : t' = j + 1 := by omega
      refine ⟨j + 1, ?_, ?_⟩
      · left
        omega
      · rwa [← ht'2]
    · have hpygt : y < p := pair_lt Fs.flatten hpy2
      have htjle : t' ≤ j := InBlock_le_of_lt ht'y hp' hpygt
      have hbad : ¬ j ≥ t' + 2 := hjf y p t' j ht'y hp' hpy2
      have hj' : j = t' + 1 := by omega
      refine ⟨t', ?_, ?_⟩
      · right
        omega
      · exact ht'y

/-! ## Existence of a minimal-length jump -/

/-- A nonempty list has an element minimising a measure. -/
lemma exists_min_measure {β : Type*} (f : β → ℕ) (l : List β) (hn : l ≠ []) :
    ∃ ab : β, ab ∈ l ∧ ∀ cd ∈ l, f cd ≥ f ab := by
  induction l with
  | nil => simp at hn
  | cons a t ih =>
      by_cases ht : t = []
      · refine ⟨a, by simp, ?_⟩
        intro cd hcd
        simp [ht] at hcd
        subst cd
        rfl
      · rcases ih ht with ⟨ab, hab, hmin⟩
        by_cases hab2 : f ab ≤ f a
        · refine ⟨ab, by simp [hab], ?_⟩
          intro cd hcd
          rw [List.mem_cons] at hcd
          rcases hcd with hcd | hcd
          · rw [hcd]
            exact hab2
          · exact hmin cd hcd
        · refine ⟨a, by simp, ?_⟩
          intro cd hcd
          rw [List.mem_cons] at hcd
          rcases hcd with hcd | hcd
          · rw [hcd]
          · have hle : f ab ≤ f cd := hmin cd hcd
            have hlt : f a < f ab := by omega
            omega

/-- A jump of minimal length exists whenever any jump exists. -/
lemma exists_minimal_jump {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hjump : ∃ i j : ℕ, IsJump Fs i j) :
    ∃ i j : ℕ, IsJump Fs i j ∧
      ∀ i' j' : ℕ, IsJump Fs i' j' → j' - i' ≥ j - i := by
  classical
  let jumps : List (ℕ × ℕ) :=
    (cancelledPairs Fs.flatten).filter (fun pr : ℕ × ℕ => IsJump Fs pr.1 pr.2)
  have hnon : jumps ≠ [] := by
    intro hz
    rcases hjump with ⟨i, j, hij⟩
    rcases hij with ⟨t, l, hi, hl, hlt, hp⟩
    have hf : (i, j) ∈ jumps := by
      simp [jumps, List.mem_filter]
      exact ⟨hp, ⟨t, l, hi, hl, hlt, hp⟩⟩
    rw [hz] at hf
    simp at hf
  rcases exists_min_measure (f := fun pr : ℕ × ℕ => pr.2 - pr.1) jumps hnon with
    ⟨ab, hab, hmin⟩
  refine ⟨ab.1, ab.2, ?_, ?_⟩
  · have hf := (List.mem_filter.mp hab).2
    simpa using hf
  · intro i' j' hij'
    have hm' : (i', j') ∈ cancelledPairs Fs.flatten := by
      rcases hij' with ⟨t, l, hi, hl, hlt, hp⟩
      exact hp
    have hf' : (i', j') ∈ jumps := by
      simp [jumps, List.mem_filter]
      exact ⟨hm', hij'⟩
    simpa using hmin (i', j') hf'

/-! ## Main theorem: a confined fully-cancelled factor exists -/

/-- With at most one survivor and at least two factors, some factor block
contains no survivor. -/
lemma exists_fully_cancelled {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hk : 2 ≤ Fs.length)
    (hsurv : (survivorPos Fs.flatten).length ≤ 1) :
    ∃ j : ℕ, j < Fs.length ∧ FullyCancelled Fs j := by
  classical
  by_cases hS : survivorPos Fs.flatten = []
  · refine ⟨0, ?_, ?_⟩
    · omega
    · intro p hp' hps
      rw [hS] at hps
      simp at hps
  · rcases hlist : survivorPos Fs.flatten with _ | ⟨s, rest⟩
    · exact False.elim (hS hlist)
    · have hsurv' : (s :: rest).length ≤ 1 := by
        rw [← hlist]
        exact hsurv
      have hrest : rest = [] := by
        have hlen : (s :: rest).length = 1 := by
          have hne : (s :: rest).length ≠ 0 := by
            intro h0
            apply hS
            rw [hlist]
            exact List.eq_nil_iff_length_eq_zero.mpr h0
          omega
        have hr0 : rest.length = 0 := by
          rw [List.length_cons] at hlen
          omega
        exact List.eq_nil_iff_length_eq_zero.mpr hr0
      have hs_mem : s ∈ survivorPos Fs.flatten := by
        rw [hlist]
        simp
      have hs_lt : s < Fs.flatten.length := survivorPos_lt_length Fs.flatten hs_mem
      rcases exists_InBlock hs_lt with ⟨t0, ht0⟩
      have hs_only : ∀ p : ℕ, p ∈ survivorPos Fs.flatten → p = s := by
        intro p hp
        rw [hlist] at hp
        simpa [hrest] using hp
      by_cases ht0z : t0 = 0
      · refine ⟨1, ?_, ?_⟩
        · omega
        · intro p hp' hps
          have hps' : p = s := hs_only p hps
          subst p
          have ht0' : InBlock Fs 0 s := by simpa [ht0z] using ht0
          have hc := InBlock_unique ht0' hp'
          omega
      · refine ⟨0, ?_, ?_⟩
        · omega
        · intro p hp' hps
          have hps' : p = s := hs_only p hps
          subst p
          have hc := InBlock_unique hp' ht0
          omega

/-- **Confined factor existence (the T1 aggregate selection).**  For a
concatenation of reduced words whose reduction has at most one letter and
which has at least two factors, some factor is confined: its block has no
survivor and every partner of every letter of the block lies in an adjacent
block. -/
theorem confined_factor_exists {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    (hk : 2 ≤ Fs.length) (hsurv : (survivorPos Fs.flatten).length ≤ 1) :
    ∃ j : ℕ, j < Fs.length ∧ Confined Fs j := by
  classical
  by_cases hjump : ∃ i j : ℕ, IsJump Fs i j
  · rcases exists_minimal_jump Fs hjump with ⟨i, j, hij⟩
    rcases hij.1 with ⟨t, l, hi, hl, hlt, hp⟩
    have hconf := confined_after_jump Fs hred hi hl hlt hp (by
      intro i' j' t' l' hi' hl' hlt' hp'
      exact hij.2 i' j' ⟨t', l', hi', hl', hlt', hp'⟩)
    refine ⟨t + 1, ?_, hconf⟩
    have hl' : l < Fs.length := hl.1
    omega
  · have hjf : JumpFree Fs := by
      intro i' j' t' l' hi' hl' hp' hlt'
      exact hjump ⟨i', j', ⟨t', l', hi', hl', hlt', hp'⟩⟩
    rcases exists_fully_cancelled Fs hk hsurv with ⟨j, hjlen, hfc⟩
    refine ⟨j, hjlen, confined_no_jump Fs hred hjf hjlen hfc⟩

end Submission.Nielsen
