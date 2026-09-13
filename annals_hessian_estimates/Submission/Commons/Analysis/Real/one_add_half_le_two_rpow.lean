import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

/-- For `x ≥ 0`, `2 ^ x` dominates the tangent-type linear lower bound `1 + x / 2`. -/
theorem one_add_half_le_two_rpow {x : ℝ} (hx : 0 ≤ x) : 1 + x / 2 ≤ 2 ^ x := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hmul : x / 2 ≤ Real.log 2 * x := by
    have := mul_le_mul_of_nonneg_right hlog hx
    linarith
  calc 1 + x / 2 = x / 2 + 1 := by ring
    _ ≤ Real.log 2 * x + 1 := by linarith
    _ ≤ Real.exp (Real.log 2 * x) := by
        have := Real.add_one_le_exp (Real.log 2 * x); linarith
    _ = 2 ^ x := by rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]

end Commons.Analysis.Real