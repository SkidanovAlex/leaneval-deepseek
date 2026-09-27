import Mathlib
import Submission.Work.EKLComp.Hcond

namespace Work.EKLC6Core

theorem integral_partition_indicator {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] {κ : Type*} [Fintype κ]
    {B : κ → Set X} (hB : Work.EKLComp.Core.IsMPart B) (c : κ → ℝ) :
    ∫ x, (∑ j, (B j).indicator (fun _ => c j) x) ∂μ = ∑ j, c j * (μ (B j)).toReal := by
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [MeasureTheory.integral_indicator_const (c j) (hB.measurable j)]
    simp [MeasureTheory.Measure.real, smul_eq_mul, mul_comm]
  · intro j _
    exact MeasureTheory.Integrable.indicator (MeasureTheory.integrable_const (c j)) (hB.measurable j)

end Work.EKLC6Core
