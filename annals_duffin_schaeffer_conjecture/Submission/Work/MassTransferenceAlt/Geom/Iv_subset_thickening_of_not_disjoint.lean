import Mathlib
import Submission.Work.MassTransferenceAlt.Basic

namespace Work.MassTransferenceAlt.Geom

open Work.MassTransferenceAlt

set_option linter.unusedVariables false

/-- If an interval `Iv x a` of radius `a` meets `U` and `2 * a < δ`, then the whole
interval sits inside the `δ`-thickening of `U`. -/
theorem Iv_subset_thickening_of_not_disjoint {x a δ : ℝ} (ha : 0 ≤ a) (h2 : 2 * a < δ)
    {U : Set ℝ} (h : ¬ Disjoint (Work.MassTransferenceAlt.Iv x a) U) :
    Work.MassTransferenceAlt.Iv x a ⊆ Metric.thickening δ U := by
  obtain ⟨y, hyA, hyU⟩ := Set.not_disjoint_iff.mp h
  intro z hz
  rw [Metric.mem_thickening_iff]
  refine ⟨y, hyU, ?_⟩
  rw [Real.dist_eq]
  rw [mem_Iv] at hz hyA
  have hz' : |z - x| ≤ a := hz
  have hy' : |x - y| ≤ a := by rw [abs_sub_comm]; exact hyA
  calc |z - y| = |(z - x) + (x - y)| := by ring_nf
    _ ≤ |z - x| + |x - y| := abs_add_le _ _
    _ ≤ a + a := by linarith
    _ = 2 * a := by ring
    _ < δ := h2

end Work.MassTransferenceAlt.Geom
