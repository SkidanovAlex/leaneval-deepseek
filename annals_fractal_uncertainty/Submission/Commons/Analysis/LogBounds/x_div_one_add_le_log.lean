import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.LogBounds

/-- For a nonnegative real `x`, the elementary bound `x / (1 + x) ≤ log (1 + x)`,
obtained from `Real.log_le_sub_one_of_pos` applied at `1 - x / (1 + x) = (1 + x)⁻¹`. -/
theorem x_div_one_add_le_log (x : ℝ) (hx : 0 ≤ x) : x / (1 + x) ≤ Real.log (1 + x) := by
  have hx1 : 0 < 1 + x := by linarith
  have hy1 : x / (1 + x) < 1 := by
    rw [div_lt_one hx1]
    linarith
  have hpos : 0 < 1 - x / (1 + x) := by linarith
  have hmain := Real.log_le_sub_one_of_pos hpos
  have h1 : 1 - x / (1 + x) = (1 + x)⁻¹ := by
    field_simp
    ring
  rw [h1] at hmain
  rw [Real.log_inv] at hmain
  have h2 : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by
    field_simp
    ring
  rw [h2] at hmain
  linarith

end Commons.Analysis.LogBounds