import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Sector.secPermDefs`

Vocabulary for the **permutation invariance of the sector projections**.

The target is `Work.BoseFixB2.Sector.secProj_contDiff_symm`: for a smooth,
permutation invariant `Φ : X n → ℝ`, the state `secProj ℓ k Φ = Σ_{|S|=k} E_S Φ`
is again smooth and permutation invariant.

Smoothness is a finite sum of `jointProj_contDiff`s; the mathematical content is
the invariance.  Each single joint projection `E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j` is
the composition of the slot operators of `S` in the *increasing* slot order (the
recursion `blockOp`).  The permutation `σ` acts on slot operators by

  `(aP ℓ i Ψ) ∘ actPerm σ = aP ℓ (σ i) (Ψ ∘ actPerm σ)`

(`aP_actPerm`/`aQ_actPerm` below — a pure `Function.update` computation, no
analysis), so conjugating `E_S` applies the same slot operators but in the order
`σ(0), σ(1), …, σ(n−1)`.  The individual `E_S` are **not** permutation invariant
(e.g. `E_{0} = Q_0P_1` on two particles is `x ↦ f x₁ − c`, which is not
symmetric), but the *sum over all `k`-subsets* is, because (i) slot operators of
distinct slots commute (`aP_comm`, `aP_aQ_comm`, `aQ_comm`), so the composite of
a family of slot operators does not depend on the order in which they are
applied, and (ii) `S ↦ σ • S` is a bijection of the `k`-subsets of `{0,…,n−1}`.

## The objects

* `slotOp ℓ j b` — the operator at slot `j`: `aQ ℓ j` if `b = true`, else `aP ℓ j`.
* `blockOpL ℓ L Φ` — the iterated composition of `slotOp`s along the list `L`,
  the head of the list being applied **last** (so that a list
  `(n−1,·) :: … :: (0,·)` reproduces `blockOp ℓ S n`).
* `stdList S k` — the standard list `(k−1, [k−1 ∈ S]), …, (0, [0 ∈ S])` of the
  recursion `blockOp ℓ S k`; `blockOp_eq_blockOpL` identifies the two.
* `conjList σ L` — the list whose slot `m` is transported to slot `σ m`.
* `kindSet L` — the set of slots carrying the flag `true`.
* `slotMap σ S` — the image of the slot set `S` under the slot permutation `σ`
  (`S` is first intersected with `{0,…,n−1}`).

## The engine

`blockOpL_conj` is the conjugation of the iterated composition under a particle
relabelling: with `Φ` arbitrary,

  `(blockOpL ℓ L Φ) ∘ actPerm σ = blockOpL ℓ (conjList σ L) (Φ ∘ actPerm σ)`.

It is a plain induction on the list, using only `aP_actPerm`/`aQ_actPerm` — no
commutation.  Combined with the *reordering* lemma (the composite of a list of
slot operators with distinct slots depends only on the set of pairs, which is
where `aP_comm`/`aP_aQ_comm`/`aQ_comm` enter) and with `Φ ∘ actPerm σ = Φ` for a
symmetric `Φ`, it yields the conjugation of the joint projection
`jointProj ℓ S Φ ∘ actPerm σ = jointProj ℓ (slotMap σ S) Φ` used to sum the
sectors.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixB2.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The slot permutation and the slot operators -/

/-- Relabelling the particles commutes with replacing the entry of slot `σ i`:
`actPerm σ (x with slot (σ i) replaced by y) = (actPerm σ x) with slot i replaced by y`. -/
lemma actPerm_update {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : X n) (i : Fin n) (y : ℝ³) :
    actPerm n σ (Function.update x (σ i) y) = Function.update (actPerm n σ x) i y := by
  funext j
  by_cases h : j = i
  · subst h
    simp [actPerm]
  · have h2 : σ j ≠ σ i := fun hh => h (σ.injective hh)
    simp [actPerm, h, h2]

/-- **The slot mean commutes with the permutation action.**  Averaging slot `i` of
`Ψ` and then relabelling the particles is the same as relabelling first and
averaging the slot `σ i`: `(aP ℓ i Ψ) ∘ actPerm σ = aP ℓ (σ i) (Ψ ∘ actPerm σ)`. -/
lemma aP_actPerm {n : ℕ} (ℓ : ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) (Ψ : X n → ℝ) :
    (fun x => aP ℓ i Ψ (actPerm n σ x))
      = fun x => aP ℓ (σ i) (fun y => Ψ (actPerm n σ y)) x := by
  funext x
  simp only [aP]
  congr 1
  rw [MeasureTheory.integral_congr_ae]
  filter_upwards with y
  rw [actPerm_update]

/-- Complement of the slot mean: `(aQ ℓ i Ψ) ∘ actPerm σ = aQ ℓ (σ i) (Ψ ∘ actPerm σ)`. -/
lemma aQ_actPerm {n : ℕ} (ℓ : ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) (Ψ : X n → ℝ) :
    (fun x => aQ ℓ i Ψ (actPerm n σ x))
      = fun x => aQ ℓ (σ i) (fun y => Ψ (actPerm n σ y)) x := by
  funext x
  simp only [aQ]
  rw [show aP ℓ i Ψ (actPerm n σ x) = aP ℓ (σ i) (fun y => Ψ (actPerm n σ y)) x from
    congrFun (aP_actPerm ℓ σ i Ψ) x]

/-- The single-slot operator at slot `j`: the complement projection `aQ ℓ j` if
`b = true` and the mean projection `aP ℓ j` if `b = false`. -/
noncomputable def slotOp (ℓ : ℝ) {n : ℕ} (j : Fin n) (b : Bool) :
    (X n → ℝ) → (X n → ℝ) :=
  bif b then aQ ℓ j else aP ℓ j

@[simp] lemma slotOp_true {n : ℕ} (ℓ : ℝ) (j : Fin n) : slotOp ℓ j true = aQ ℓ j := rfl

@[simp] lemma slotOp_false {n : ℕ} (ℓ : ℝ) (j : Fin n) : slotOp ℓ j false = aP ℓ j := rfl

/-! ## 2. Iterated slot operators along a list -/

/-- **Iterated composition of slot operators along a list.**  The head of the list
is applied *last*: `blockOpL ℓ (p :: L) Φ = slotOp ℓ p.1 p.2 (blockOpL ℓ L Φ)`
(the entry `p` is ignored when its slot is `≥ n`, matching `blockOp`). -/
noncomputable def blockOpL (ℓ : ℝ) {n : ℕ} : List (ℕ × Bool) → (X n → ℝ) → (X n → ℝ)
  | [], Φ => Φ
  | (p :: L), Φ =>
      if h : p.1 < n then slotOp ℓ ⟨p.1, h⟩ p.2 (blockOpL ℓ L Φ) else blockOpL ℓ L Φ

@[simp] lemma blockOpL_nil (ℓ : ℝ) {n : ℕ} (Φ : X n → ℝ) : blockOpL ℓ [] Φ = Φ := rfl

lemma blockOpL_cons {ℓ : ℝ} {n : ℕ} (p : ℕ × Bool) (L : List (ℕ × Bool)) (Φ : X n → ℝ) :
    blockOpL ℓ (p :: L) Φ
      = if h : p.1 < n then slotOp ℓ ⟨p.1, h⟩ p.2 (blockOpL ℓ L Φ)
        else blockOpL ℓ L Φ := rfl

lemma blockOpL_cons_of_lt {ℓ : ℝ} {n : ℕ} {p : ℕ × Bool} {L : List (ℕ × Bool)}
    (h : p.1 < n) (Φ : X n → ℝ) :
    blockOpL ℓ (p :: L) Φ = slotOp ℓ ⟨p.1, h⟩ p.2 (blockOpL ℓ L Φ) := by
  rw [blockOpL_cons, dif_pos h]

/-- The iterated composition is `blockOp` read on the standard list: the entries
`(k−1, [k−1 ∈ S]), …, (0, [0 ∈ S])` (head applied last) reproduce the recursion
`blockOp ℓ S k`. -/
def stdList (S : Finset ℕ) : ℕ → List (ℕ × Bool)
  | 0 => []
  | (k + 1) => (k, decide (k ∈ S)) :: stdList S k

@[simp] lemma stdList_zero (S : Finset ℕ) : stdList S 0 = [] := rfl

@[simp] lemma stdList_succ (S : Finset ℕ) (k : ℕ) :
    stdList S (k + 1) = (k, decide (k ∈ S)) :: stdList S k := rfl

@[simp] lemma stdList_length (S : Finset ℕ) : ∀ k, (stdList S k).length = k
  | 0 => rfl
  | (k + 1) => by simp [stdList_length S k]

lemma mem_stdList {S : Finset ℕ} {k : ℕ} {p : ℕ × Bool} :
    p ∈ stdList S k ↔ ∃ m < k, p = (m, decide (m ∈ S)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [stdList_succ, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨m, hm, hp⟩)
        · exact ⟨k, Nat.lt_succ_self k, h⟩
        · exact ⟨m, Nat.lt_succ_of_lt hm, hp⟩
      · rintro ⟨m, hm, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
        · exact Or.inr ⟨m, hm, hp⟩
        · exact Or.inl hp

lemma stdList_slot_lt {S : Finset ℕ} {k : ℕ} {p : ℕ × Bool} (hp : p ∈ stdList S k) :
    p.1 < k := by
  obtain ⟨m, hm, rfl⟩ := mem_stdList.mp hp
  exact hm

lemma blockOp_eq_blockOpL {ℓ : ℝ} {n : ℕ} (S : Finset ℕ) :
    ∀ (k : ℕ) {Φ : X n → ℝ}, blockOp ℓ S k Φ = blockOpL ℓ (stdList S k) Φ := by
  intro k
  induction k with
  | zero => intro Φ; rfl
  | succ k ih =>
      intro Φ
      by_cases hkn : k < n
      · rw [blockOp_succ S hkn, ih, stdList_succ, blockOpL_cons_of_lt hkn]
        by_cases hmem : k ∈ S
        · rw [if_pos hmem]
          simp [slotOp, hmem]
        · rw [if_neg hmem]
          simp [slotOp, hmem]
      · have hstep : blockOp ℓ S (k + 1) Φ = blockOp ℓ S k Φ := by
          rw [blockOp]
          simp only [dif_neg hkn]
        rw [hstep, ih, stdList_succ, blockOpL_cons, dif_neg hkn]

/-! ## 3. Transporting the slots along a particle permutation -/

/-- **The conjugated list**: every slot `m` of the list is transported to slot `σ m`
(entries with slot `≥ n` are left alone; they are ignored by `blockOpL`). -/
noncomputable def conjList {n : ℕ} (σ : Equiv.Perm (Fin n)) (L : List (ℕ × Bool)) :
    List (ℕ × Bool) :=
  L.map (fun p => if h : p.1 < n then ((σ ⟨p.1, h⟩).val, p.2) else p)

/-- **Conjugation of the iterated composition.**  Relabelling the particles
transports every slot of the list along `σ`:

  `(blockOpL ℓ L Φ) ∘ actPerm σ = blockOpL ℓ (conjList σ L) (Φ ∘ actPerm σ)`.

This is an induction on the list (`blockOpL_conj`); it uses only the slot-mean
computation `aP_actPerm`/`aQ_actPerm`, and no commutation of slot operators. -/
lemma blockOpL_conj {n : ℕ} (ℓ : ℝ) (σ : Equiv.Perm (Fin n)) (Φ : X n → ℝ) :
    ∀ L : List (ℕ × Bool),
      (fun x => blockOpL ℓ L Φ (actPerm n σ x))
        = blockOpL ℓ (conjList σ L) (fun x => Φ (actPerm n σ x)) := by
  intro L
  induction L with
  | nil => rfl
  | cons p L ih =>
      rcases p with ⟨m, b⟩
      by_cases hm : m < n
      · have hσfin : (σ ⟨m, hm⟩).val < n := (σ ⟨m, hm⟩).isLt
        simp only [blockOpL, conjList, List.map_cons, dif_pos hm, dif_pos hσfin]
        have hfun : (fun x => slotOp ℓ ⟨m, hm⟩ b (blockOpL ℓ L Φ) (actPerm n σ x))
            = slotOp ℓ (σ ⟨m, hm⟩) b (fun y => blockOpL ℓ L Φ (actPerm n σ y)) := by
          cases b
          · simpa using aP_actPerm ℓ σ ⟨m, hm⟩ (blockOpL ℓ L Φ)
          · simpa using aQ_actPerm ℓ σ ⟨m, hm⟩ (blockOpL ℓ L Φ)
        rw [hfun, ih]
        simp only [conjList]
      · simp only [blockOpL, conjList, List.map_cons, dif_neg hm]
        exact ih

/-! ## 4. Slot sets -/

/-- The set of slots of the list carrying the flag `true`. -/
noncomputable def kindSet (L : List (ℕ × Bool)) : Finset ℕ :=
  ((L.filter (fun p => p.2)).map Prod.fst).toFinset

lemma mem_kindSet {L : List (ℕ × Bool)} {j : ℕ} :
    j ∈ kindSet L ↔ ∃ p ∈ L, p.2 = true ∧ p.1 = j := by
  simp only [kindSet, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hp2⟩, hp1⟩
    exact ⟨p, hp, hp2, hp1⟩
  · rintro ⟨p, hp, hp2, hp1⟩
    exact ⟨p, ⟨hp, hp2⟩, hp1⟩

/-- **The image of the slot set `S` under the slot permutation `σ`** (the slots
outside `{0,…,n−1}` are discarded). -/
noncomputable def slotMap {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset ℕ) : Finset ℕ :=
  (S ∩ Finset.range n).image (fun m => if h : m < n then (σ ⟨m, h⟩).val else 0)

lemma mem_slotMap {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset ℕ) (j : ℕ) :
    j ∈ slotMap σ S ↔ ∃ m ∈ S, ∃ h : m < n, (σ ⟨m, h⟩).val = j := by
  simp only [slotMap, Finset.mem_image, Finset.mem_inter, Finset.mem_range]
  constructor
  · rintro ⟨m, ⟨hmS, hmn⟩, hmj⟩
    rw [dif_pos hmn] at hmj
    exact ⟨m, hmS, hmn, hmj⟩
  · rintro ⟨m, hmS, hmn, hmj⟩
    exact ⟨m, ⟨hmS, hmn⟩, by rw [dif_pos hmn]; exact hmj⟩

lemma slotMap_subset_range {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset ℕ) :
    slotMap σ S ⊆ Finset.range n := by
  intro j hj
  rw [mem_slotMap] at hj
  obtain ⟨m, -, hmn, hmj⟩ := hj
  rw [Finset.mem_range, ← hmj]
  exact (σ ⟨m, hmn⟩).isLt

end Work.BoseFixB2.Sector
