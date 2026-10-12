import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.SectorAux.boxCompTOrthMeas
import Submission.Work.BoseFixB1S.hopSlotOrth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.SectorAux.weightedOrthMemSGood`

The weighted orthogonality of the three-way box components, in the `GoodState` form:

    ∫_{abox N ℓ} (boxCompT S T Φ)(g(x i))(boxCompT S' T' Ψ) = 0

whenever `j ∈ S`, `j ∉ S'` and the weight lives in a slot `i ≠ j`.

This is exactly `Work.BoseFixB1S.weighted_orth_of_mem_S` with the continuity hypotheses on `Φ`,
`Ψ` replaced by `GoodState` (measurable and bounded on the box).  `weighted_orth_of_mem_S` uses
continuity only to *manufacture* `goodState_of_continuous`; the actual proof consumes only the
`GoodState` interface:

* `goodState_boxCompT` (components of `GoodState`s are `GoodState`s),
* the `Pⱼ`-eigenvector rule with `GoodState` input (`boxPInd_boxCompT_good`, proved in the
  sibling module `boxCompTOrthMeas`),
* self-adjointness of `Pⱼ` (`boxPIndSelfAdjoint`, already stated for measurable, box-bounded
  states) and the commutation of `Pⱼ` with a weight in another slot
  (`Gen.boxPInd_slotWeight`).

Replacing the two `boxPInd_boxCompT` calls by `boxPInd_boxCompT_good` gives the proof verbatim.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

open Submission.BoseGases

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem weightedOrthMemSGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : Measurable g) {Bg : ℝ}
    (hgb : ∀ z ∈ Submission.BoseGases.acube ℓ, |g z| ≤ Bg)
    {i j : Fin N} (hij : j ≠ i)
    {S T S' T' : Finset (Fin N)} (hjS : j ∈ S) (hjS' : j ∉ S')
    {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  obtain ⟨hXm, CX, hXb⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc S T hΦ
  obtain ⟨hYm, CY, hYb⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc S' T' hΨ
  have hWm : Measurable (fun x : Submission.BoseGases.X N => g (x i)
      * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) :=
    (hgm.comp (measurable_pi_apply i)).mul hYm
  have hWb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |g (x i) * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x| ≤ max Bg 0 * max CY 0 := by
    intro x hx
    rw [abs_mul]
    refine mul_le_mul
      (le_trans (hgb (x i) ((mem_abox_iff N ℓ x).mp hx i)) (le_max_left _ _))
      (le_trans (hYb x hx) (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hSA := Work.BoseFixB1S.boxPIndSelfAdjoint hℓ hvol hA hvolA hAc j hXm hXb hWm hWb
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
            * (g (x i) * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) := by
        apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        intro x hx
        change Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
            * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x
          = Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
              * (g (x i) * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
        rw [boxPInd_boxCompT_good hℓ hvol hA hvolA hAc S T hΦ j x hx, if_pos hjS]
        ring
    _ = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxCompT volA A S T Φ x
            * Work.UBBInputs8.boxPInd volA A j (fun y => g (y i)
                * Work.BoseFixB1S.boxCompT volA A S' T' Ψ y) x := hSA
    _ = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxCompT volA A S T Φ x
            * (g (x i) * Work.UBBInputs8.boxPInd volA A j
                (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x) := by
        apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        intro x hx
        change Work.BoseFixB1S.boxCompT volA A S T Φ x
            * Work.UBBInputs8.boxPInd volA A j (fun y => g (y i)
                * Work.BoseFixB1S.boxCompT volA A S' T' Ψ y) x
          = Work.BoseFixB1S.boxCompT volA A S T Φ x
            * (g (x i) * Work.UBBInputs8.boxPInd volA A j
                (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x)
        rw [Work.BoseFixB1S.Gen.boxPInd_slotWeight volA A (Ne.symm hij)
          (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x]
    _ = 0 := by
        have hz : (∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1S.boxCompT volA A S T Φ x
              * (g (x i) * Work.UBBInputs8.boxPInd volA A j
                  (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x))
            = ∫ x in Submission.BoseGases.abox N ℓ,
                (0 : Submission.BoseGases.X N → ℝ) x := by
          apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
          intro x hx
          change Work.BoseFixB1S.boxCompT volA A S T Φ x
              * (g (x i) * Work.UBBInputs8.boxPInd volA A j
                  (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x) = 0
          rw [boxPInd_boxCompT_good hℓ hvol hA hvolA hAc S' T' hΨ j x hx, if_neg hjS']
          ring
        rw [hz]
        simp

end Work.BoseFixB1.SectorAux
