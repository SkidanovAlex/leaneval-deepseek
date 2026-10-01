import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

/-- The `N`-th harmonic sum is at most `1 + log N`. -/
theorem harmonic_sum_le_one_add_log (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  have h := harmonic_le_one_add_log N
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simpa only [one_div] using h

end Work.LinnikAreas
