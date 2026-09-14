import Mathlib.Analysis.Real.Sqrt

namespace Commons.Analysis.Real

theorem sqrt_four_mul {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [Real.sqrt_mul' 4 hx, h4]

end Commons.Analysis.Real