import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxPInd_boxQInd_pointwise`

The `PQ` pattern of the FS box projections, in the orientation `P_iQ_j`, written with the
one-slot mean `oneMean` and the two-slot mean `twoMean` (`BoxPotOper`):

  `P_iQ_jΦ = 1_A(x_i)·1_A(x_j)·(oneMeanᵢΦ − twoMeanᵢⱼΦ)`   (`boxPInd_boxQInd_twoMean`),

together with the mean forms of the two other ingredients

  `P_iΦ = 1_A(x_i)·oneMeanᵢΦ`                               (`boxPInd_eq`),
  `P_iP_jΦ = 1_A(x_i)·1_A(x_j)·twoMeanᵢⱼΦ`                  (`boxPInd_twoMean`),

immediately give the pointwise identity requested here:

  `P_iQ_jΦ = 1_A(x_j)·(P_iΦ − P_iP_jΦ)`

(the two sides differ only by `1_A(x_j)² = 1_A(x_j)`, since the box indicator is idempotent).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

theorem boxPInd_boxQInd_pointwise {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
        = A.indicator (fun _ => (1 : ℝ)) (x j) *
            (Work.UBBInputs8.boxPInd volA A i Φ x
              - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) := by
  intro x hx
  rw [boxPInd_boxQInd_twoMean (volA := volA) hℓ hvol hA hvolA hAc hij hΦc x hx,
    boxPInd_twoMean (volA := volA) A hij Φ x,
    boxPInd_eq (volA := volA) A i Φ x]
  unfold Aind
  by_cases hxj : x j ∈ A
  · simp only [Set.indicator_of_mem hxj, one_mul]
    ring
  · simp only [Set.indicator_of_notMem hxj, zero_mul]
    ring

end Work.BoseFixB1S
