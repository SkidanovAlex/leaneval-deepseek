import Mathlib

namespace Work.FIArea7

/-- The harmonic sum over `Icc 1 y` is at most `1 + log y` for every `y : ℕ`
(in particular the statement is trivial for `y = 0`, since then the sum is empty). -/
theorem sum_inv_Icc_le_one_add_log (y : ℕ) :
    ∑ n ∈ Finset.Icc 1 y, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log y := by
  have h := harmonic_le_one_add_log y
  have hsum : ((harmonic y : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 y, (1 : ℝ) / (n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp [one_div]
  rw [← hsum]
  exact h

end Work.FIArea7
