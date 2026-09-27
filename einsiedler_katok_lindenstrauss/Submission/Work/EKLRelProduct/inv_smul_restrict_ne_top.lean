import Mathlib

open MeasureTheory

namespace Work.EKLRelProduct

theorem inv_smul_restrict_ne_top {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {S : Set α} (h0 : μ S ≠ 0) (htop : μ S ≠ ⊤) (t : Set α) :
    ((μ S)⁻¹ • μ.restrict S) t ≠ ⊤ := by
  -- The restricted measure is bounded by `μ S` because `univ` is measurable.
  have hle : (μ.restrict S) t ≤ μ S := by
    calc (μ.restrict S) t ≤ (μ.restrict S) Set.univ := measure_mono (Set.subset_univ t)
      _ = μ S := by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [Measure.smul_apply, smul_eq_mul]
  refine ne_top_of_lt (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
  calc (μ S)⁻¹ * (μ.restrict S) t ≤ (μ S)⁻¹ * μ S := mul_le_mul_right hle _
    _ = 1 := ENNReal.inv_mul_cancel h0 htop

end Work.EKLRelProduct
