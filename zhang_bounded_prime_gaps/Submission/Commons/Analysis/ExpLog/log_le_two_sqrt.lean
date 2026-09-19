import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.ExpLog

/-- For every nonnegative real `x`, `log x ≤ 2 * √x`.

Proof: with `t = √x ≥ 0`, `x = t²`, and `log(t²) = 2 log t ≤ 2t = 2√x`,
using the elementary bound `log t ≤ t` for `t ≥ 0`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsqrt : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx]
    ring
  rw [hsqrt]
  exact mul_le_mul_of_nonneg_left (Real.log_le_self (Real.sqrt_nonneg x)) (by norm_num)

end Commons.Analysis.ExpLog