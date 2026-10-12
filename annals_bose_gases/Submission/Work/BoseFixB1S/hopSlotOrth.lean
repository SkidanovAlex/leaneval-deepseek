import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxFlatAux
import Submission.Work.BoseFixB1S.Gen.boxPInd_slotWeight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.hopSlotOrth` — weighted orthogonality of the joint components

The weighted form of `boxCompT_orth`: if the slot types (`orthSlotType` = `0` on `S`, `1` on `T`,
`2` outside `S ∪ T`) of two disjoint pairs `(S,T)`, `(S',T')` differ in a slot `j ≠ i`, then the
components are orthogonal *with a weight in the slot `i`*:

    ∫_{abox N ℓ} (boxCompT S T Φ)(g(x i))(boxCompT S' T' Ψ) = 0 .

The proof is the case analysis of `boxCompT_orth` with the extra factor `g(x i)`:
* the two "one slot is `P`, the other is not" cases use self-adjointness of `Pⱼ` together with
  `Gen.boxPInd_slotWeight`: the weight lives in the slot `i ≠ j`, so it is constant along the
  `j`-fibre and comes out of the `A`-mean, `Pⱼ(g(· i)·Y) = g(x i)·PⱼY`;
* the two "one slot is `Rⱼ = 1 − 1_A(xⱼ)`, the other is not" cases vanish pointwise because the two
  components are supported on the complementary half-spaces `{xⱼ ∉ A}` / `{xⱼ ∈ A}`
  (`boxComponent_vanish_off` / `boxComponent_vanish_on`, from `boxCompT_orth`), the weight being
  irrelevant to the vanishing.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The `P`-slot case, with the weight -/

/-- If `j ∈ S` and `j ∉ S'`, the two components are orthogonal against the weight `g(x i)`
(the slot `i` of the weight is different from the slot `j` where the components are distinguished
as a `P`-slot versus a non-`P`-slot). -/
theorem weighted_orth_of_mem_S {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : Measurable g) {Bg : ℝ}
    (hgb : ∀ z ∈ Submission.BoseGases.acube ℓ, |g z| ≤ Bg)
    {i j : Fin N} (hij : j ≠ i)
    {S T S' T' : Finset (Fin N)} (hjS : j ∈ S) (hjS' : j ∉ S')
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  obtain ⟨hXm, CX, hXb⟩ :=
    goodState_boxCompT hℓ hvol hA hvolA hAc S T (goodState_of_continuous hℓ hΦc)
  obtain ⟨hYm, CY, hYb⟩ :=
    goodState_boxCompT hℓ hvol hA hvolA hAc S' T' (goodState_of_continuous hℓ hΨc)
  have hWm : Measurable (fun x : Submission.BoseGases.X N => g (x i)
      * boxCompT volA A S' T' Ψ x) :=
    (hgm.comp (measurable_pi_apply i)).mul hYm
  have hWb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |g (x i) * boxCompT volA A S' T' Ψ x| ≤ max Bg 0 * max CY 0 := by
    intro x hx
    rw [abs_mul]
    refine mul_le_mul
      (le_trans (hgb (x i) ((mem_abox_iff N ℓ x).mp hx i)) (le_max_left _ _))
      (le_trans (hYb x hx) (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hSA := boxPIndSelfAdjoint hℓ hvol hA hvolA hAc j hXm hXb hWm hWb
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        boxCompT volA A S T Φ x * g (x i) * boxCompT volA A S' T' Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          UBBInputs8.boxPInd volA A j (boxCompT volA A S T Φ) x
            * (g (x i) * boxCompT volA A S' T' Ψ x) := by
        apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        intro x hx
        change boxCompT volA A S T Φ x * g (x i) * boxCompT volA A S' T' Ψ x
          = UBBInputs8.boxPInd volA A j (boxCompT volA A S T Φ) x
              * (g (x i) * boxCompT volA A S' T' Ψ x)
        rw [boxPInd_boxCompT hℓ hvol hA hvolA hAc S T hΦc j x hx, if_pos hjS]
        ring
    _ = ∫ x in Submission.BoseGases.abox N ℓ,
          boxCompT volA A S T Φ x
            * UBBInputs8.boxPInd volA A j (fun y => g (y i)
                * boxCompT volA A S' T' Ψ y) x := hSA
    _ = ∫ x in Submission.BoseGases.abox N ℓ,
          boxCompT volA A S T Φ x
            * (g (x i) * UBBInputs8.boxPInd volA A j (boxCompT volA A S' T' Ψ) x) := by
        apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        intro x hx
        change boxCompT volA A S T Φ x
            * UBBInputs8.boxPInd volA A j (fun y => g (y i)
                * boxCompT volA A S' T' Ψ y) x
          = boxCompT volA A S T Φ x
            * (g (x i) * UBBInputs8.boxPInd volA A j (boxCompT volA A S' T' Ψ) x)
        rw [Gen.boxPInd_slotWeight volA A (Ne.symm hij) (boxCompT volA A S' T' Ψ) x]
    _ = 0 := by
        have hz : (∫ x in Submission.BoseGases.abox N ℓ,
            boxCompT volA A S T Φ x
              * (g (x i) * UBBInputs8.boxPInd volA A j (boxCompT volA A S' T' Ψ) x))
            = ∫ x in Submission.BoseGases.abox N ℓ, (0 : Submission.BoseGases.X N → ℝ) x := by
          apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
          intro x hx
          change boxCompT volA A S T Φ x
              * (g (x i) * UBBInputs8.boxPInd volA A j (boxCompT volA A S' T' Ψ) x) = 0
          rw [boxPInd_boxCompT hℓ hvol hA hvolA hAc S' T' hΨc j x hx, if_neg hjS']
          ring
        rw [hz]
        simp

/-! ## The main theorem -/

theorem hopSlotOrth {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : Measurable g) {Bg : ℝ}
    (hgb : ∀ z ∈ Submission.BoseGases.acube ℓ, |g z| ≤ Bg)
    {i j : Fin N} (hij : j ≠ i)
    {S T S' T' : Finset (Fin N)} (hST : Disjoint S T) (hST' : Disjoint S' T')
    (hdif : Work.BoseFixB1S.orthSlotType S T j ≠ Work.BoseFixB1S.orthSlotType S' T' j)
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  have hswap : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxCompT volA A S' T' Ψ x * g (x i)
            * Work.BoseFixB1S.boxCompT volA A S T Φ x := by
    apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
    intro x hx
    ring
  by_cases hS : j ∈ S
  · by_cases hS' : j ∈ S'
    · exact absurd (by unfold orthSlotType; rw [if_pos hS, if_pos hS']) hdif
    · exact weighted_orth_of_mem_S hℓ hvol hA hvolA hAc hgm hgb hij hS hS' hΦc hΨc
  · by_cases hS' : j ∈ S'
    · rw [hswap]
      exact weighted_orth_of_mem_S hℓ hvol hA hvolA hAc hgm hgb hij hS' hS hΨc hΦc
    · by_cases hT : j ∈ T
      · have hT' : j ∉ T' := fun h =>
          hdif (by unfold orthSlotType; rw [if_neg hS, if_pos hT, if_neg hS', if_pos h])
        have hnot : j ∉ S' ∪ T' := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS', hT'⟩
        refine integral_mul_eq_zero_of_vanish (A := A) (j := j)
          (F := fun x => Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i))
          (G := Work.BoseFixB1S.boxCompT volA A S' T' Ψ) ?_ ?_
        · intro x hx
          rw [boxComponent_vanish_off volA A (Finset.mem_union_right S hT) Φ x hx, zero_mul]
        · exact boxComponent_vanish_on volA A hnot Ψ
      · have hT' : j ∈ T' := by
          by_contra h
          exact hdif (by unfold orthSlotType; rw [if_neg hS, if_neg hT, if_neg hS', if_neg h])
        have hnot : j ∉ S ∪ T := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS, hT⟩
        rw [hswap]
        refine integral_mul_eq_zero_of_vanish (A := A) (j := j)
          (F := fun x => Work.BoseFixB1S.boxCompT volA A S' T' Ψ x * g (x i))
          (G := Work.BoseFixB1S.boxCompT volA A S T Φ) ?_ ?_
        · intro x hx
          rw [boxComponent_vanish_off volA A (Finset.mem_union_right S' hT') Ψ x hx, zero_mul]
        · exact boxComponent_vanish_on volA A hnot Φ

end Work.BoseFixB1S
