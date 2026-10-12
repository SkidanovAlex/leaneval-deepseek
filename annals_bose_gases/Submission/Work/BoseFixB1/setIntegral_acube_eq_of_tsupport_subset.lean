import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxOpA
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem setIntegral_acube_eq_of_tsupport_subset {a : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hsh : tsupport h ⊆ A)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ y in Submission.BoseGases.acube a, h y * g y) = ∫ y in A, h y * g y := by
  rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable a),
      ← MeasureTheory.integral_indicator hAm]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ A
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hAc hy)]
  · have hzy : h y = 0 := by
      by_contra hne
      exact hy (hsh (subset_tsupport h (Function.mem_support.mpr hne)))
    by_cases hyc : y ∈ Submission.BoseGases.acube a
    · rw [Set.indicator_of_mem hyc, Set.indicator_of_notMem hy, hzy, zero_mul]
    · rw [Set.indicator_of_notMem hyc, Set.indicator_of_notMem hy]

end Work.BoseFixB1
