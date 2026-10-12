import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandSlot.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.Band.Defs`

Vocabulary for the **band/level-splitting identities** of FS §6 (`eq:dvapriori`, the
displayed `d₁`, `d₂`).

FS decompose the potential part of the box word as a sum of *few-slot* multiplication
terms (`potWordU = −μΣᵢ ∫_y w(xᵢ,y) + Σ_{a<b} w(x_a,x_b)`).  For such a term living on a
slot set `A` (`|A| ≤ 2`), the matrix element of the `n₊ = k`-grading is computed by
*localising to the slots of `A`*: the projections acting on the free slots `J = [n] ∖ A`
pair up the two sides, and their resolution collapses the sum.  This module contains the
vocabulary of that computation:

* `slotList n J` — the list of slots of `J` inside `{0,…,n−1}`, in increasing order;
* `projOn ℓ J R Φ` — the **restricted slot projection**: apply `aQ ℓ j` for `j ∈ R ∩ J`
  and `aP ℓ j` for `j ∈ J ∖ R`, leaving the other slots untouched;
* the elementary invariance/multiplicativity facts about the slot means that the collapse
  of the free slots uses (none of which requires any regularity of `Φ`).
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The slot list of a finset -/

/-- The slots of `J` inside `{0,…,n−1}`, in increasing order. -/
def slotList (n : ℕ) (J : Finset ℕ) : List ℕ := (List.range n).filter (fun j => j ∈ J)

lemma slotList_nodup (n : ℕ) (J : Finset ℕ) : (slotList n J).Nodup :=
  List.Nodup.filter _ List.nodup_range

lemma mem_slotList {n : ℕ} {J : Finset ℕ} {j : ℕ} :
    j ∈ slotList n J ↔ j < n ∧ j ∈ J := by
  simp [slotList, List.mem_filter, List.mem_range]

lemma slotList_lt {n : ℕ} {J : Finset ℕ} {j : ℕ} (h : j ∈ slotList n J) : j < n :=
  (mem_slotList.mp h).1

lemma slotList_toFinset {n : ℕ} {J : Finset ℕ} (hJ : J ⊆ Finset.range n) :
    (slotList n J).toFinset = J := by
  rw [slotList, List.toFinset_filter, List.toFinset_range]
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h; exact of_decide_eq_true h.2
  · intro h; exact ⟨Finset.mem_range.mp (hJ h), decide_eq_true h⟩

lemma slotList_range (n : ℕ) : slotList n (Finset.range n) = List.range n := by
  simp [slotList]

lemma stdList_fst (R : Finset ℕ) (n : ℕ) :
    (Work.BoseFixB2.Sector.stdList R n).map Prod.fst = (List.range n).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.BoseFixB2.Sector.stdList_succ, List.map_cons, ih, List.range_succ,
        List.reverse_append]
      rfl


/-! ## 2. The restricted slot projection -/

/-- **The restricted slot projection.**  `projOn ℓ J R Φ` applies, for every slot
`j ∈ J ∩ {0,…,n−1}`, the operator `aQ ℓ j` if `j ∈ R` and `aP ℓ j` if `j ∉ R`; the slots
outside `J` are left untouched. -/
noncomputable def projOn (ℓ : ℝ) {n : ℕ} (J R : Finset ℕ) (Φ : X n → ℝ) : X n → ℝ :=
  slotProd ℓ (slotList n J) R Φ

lemma projOn_eq_slotProd (ℓ : ℝ) {n : ℕ} (J R : Finset ℕ) (Φ : X n → ℝ) :
    projOn ℓ J R Φ = slotProd ℓ (slotList n J) R Φ := rfl

/-- `projOn` depends on the slot pattern only through the slots of `J`. -/
lemma projOn_congr {ℓ : ℝ} {n : ℕ} {J R R' : Finset ℕ}
    (h : ∀ j ∈ slotList n J, (j ∈ R ↔ j ∈ R')) (Φ : X n → ℝ) :
    projOn ℓ J R Φ = projOn ℓ J R' Φ :=
  slotProd_congr (slotList n J) (fun _ hj => slotList_lt hj) h Φ

/-- The restricted slot projection preserves continuity. -/
lemma projOn_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (J R : Finset ℕ) {Φ : X n → ℝ}
    (hΦ : Continuous Φ) : Continuous (projOn ℓ J R Φ) :=
  slotProd_continuous hℓ _ _ hΦ

/-- On the full slot set the restricted projection is the joint sector projection. -/
lemma projOn_full {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (R : Finset ℕ) {Φ : X n → ℝ}
    (hΦ : Continuous Φ) :
    projOn ℓ (Finset.range n) R Φ = jointProj ℓ R Φ := by
  rw [projOn, slotList_range]
  show slotProd ℓ (List.range n) R Φ = Work.BoseFixB2.blockOp ℓ R n Φ
  rw [Work.BoseFixB2.Sector.blockOp_eq_blockOpL R n]
  unfold slotProd
  refine Work.BoseFixB2.Sector.blockOpL_congr_set hℓ _ _ ?_ ?_ ?_ ?_ hΦ
  · rw [show (List.map Prod.fst (List.map (fun j => (j, decide (j ∈ R))) (List.range n)))
        = List.range n from by
      rw [List.map_map]
      exact List.map_id _]
    exact List.nodup_range
  · rw [stdList_fst]
    exact List.nodup_reverse.mpr List.nodup_range
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    simpa using List.mem_range.mp hj
  · intro p
    rw [List.mem_map, Work.BoseFixB2.Sector.mem_stdList]
    constructor
    · rintro ⟨m, hm, hmp⟩
      exact ⟨m, List.mem_range.mp hm, hmp.symm⟩
    · rintro ⟨m, hm, hmp⟩
      exact ⟨m, List.mem_range.mpr hm, hmp.symm⟩

/-- The empty slot set gives the identity. -/
@[simp] lemma projOn_empty {ℓ : ℝ} {n : ℕ} (R : Finset ℕ) (Φ : X n → ℝ) :
    projOn ℓ (∅ : Finset ℕ) R Φ = Φ := by
  rw [projOn, slotList]
  simp

/-! ## 3. Elementary invariance and multiplicativity of the slot means

None of these uses any regularity of `Φ`; `aP ℓ j` is *defined* as the mean over the
slot-`j` box and hence (i) is constant along the `j`-th coordinate and (ii) pulls out any
factor that is constant along the `j`-th coordinate. -/

lemma update_update_same {n : ℕ} (x : X n) (j : Fin n)
    (z y : EuclideanSpace ℝ (Fin 3)) :
    Function.update (Function.update x j z) j y = Function.update x j y := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [Function.update_apply, h]

/-- The slot mean in slot `j` is constant along the `j`-th coordinate. -/
lemma aP_invariant_slot {ℓ : ℝ} {n : ℕ} (j : Fin n) (Φ : X n → ℝ) (x : X n)
    (z : EuclideanSpace ℝ (Fin 3)) :
    aP ℓ j Φ (Function.update x j z) = aP ℓ j Φ x := by
  show (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (Function.update (Function.update x j z) j y))
      = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (Function.update x j y))
  congr 1
  have hh : (fun y => Φ (Function.update (Function.update x j z) j y))
      = (fun y => Φ (Function.update x j y)) := by
    funext y; rw [update_update_same]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => congrFun hh y))

/-- A factor that is constant along the `j`-th coordinate pulls out of the slot mean. -/
lemma aP_mul_invariant {ℓ : ℝ} {n : ℕ} (j : Fin n) {W : X n → ℝ}
    (hW : ∀ (x : X n) (z : EuclideanSpace ℝ (Fin 3)),
      W (Function.update x j z) = W x)
    (Ψ : X n → ℝ) (x : X n) :
    aP ℓ j (fun y => W y * Ψ y) x = W x * aP ℓ j Ψ x := by
  show (1 / ℓ ^ 3) * (∫ y in acube ℓ, W (Function.update x j y) * Ψ (Function.update x j y))
      = W x * ((1 / ℓ ^ 3) * ∫ y in acube ℓ, Ψ (Function.update x j y))
  have h1 : (∫ y in acube ℓ, W (Function.update x j y) * Ψ (Function.update x j y))
      = ∫ y in acube ℓ, W x * Ψ (Function.update x j y) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [hW x y]
  rw [h1, MeasureTheory.integral_const_mul]
  ring

/-- The complement of the slot mean has vanishing slot mean. -/
lemma aP_aQ_slot_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) {ζ : X n → ℝ}
    (hζ : Continuous ζ) : aP ℓ j (aQ ℓ j ζ) = 0 :=
  Work.BoseFixB2.Sector.aP_aQ_self_eq_zero hℓ j hζ

/-- The product of a slot-`j`-invariant factor with a slot-`j`-mean-free factor is
slot-`j`-mean-free. -/
lemma aP_invariant_mul_meanFree {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) {W : X n → ℝ}
    (hW : ∀ (x : X n) (z : EuclideanSpace ℝ (Fin 3)),
      W (Function.update x j z) = W x)
    {ζ : X n → ℝ} (hζ : Continuous ζ) :
    aP ℓ j (fun y => W y * aQ ℓ j ζ y) = 0 := by
  funext x
  rw [aP_mul_invariant j hW (aQ ℓ j ζ) x, congrFun (aP_aQ_slot_eq_zero hℓ j hζ) x]
  simp

end

end Work.BoseFixB2.DvApriori
