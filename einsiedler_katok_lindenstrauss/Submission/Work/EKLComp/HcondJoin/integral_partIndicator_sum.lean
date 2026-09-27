import Mathlib
import Submission.Work.EKLComp.Hcond

namespace Work.EKLComp.HcondJoin

theorem integral_partIndicator_sum {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {ι : Type} [Fintype ι] {A : ι → Set X}
    (hA : Work.EKLComp.Core.IsMPart A) (c : ι → ℝ) :
    ∫ x, (∑ i, (A i).indicator (fun _ => c i) x) ∂μ = ∑ i, (μ (A i)).toReal * c i := by
  classical
  have hint : ∀ i, MeasureTheory.Integrable (fun x => (A i).indicator (fun _ => c i) x) μ := by
    intro i
    refine MeasureTheory.Integrable.of_bound
      ((measurable_const.indicator (hA.measurable i)).aestronglyMeasurable) ‖c i‖ ?_
    filter_upwards with x
    by_cases hx : x ∈ A i
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_indicator_const (c i) (hA.measurable i)]
  simp [MeasureTheory.Measure.real]

end Work.EKLComp.HcondJoin
