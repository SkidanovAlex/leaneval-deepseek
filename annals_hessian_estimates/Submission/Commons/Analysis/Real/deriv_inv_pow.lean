import Mathlib.Analysis.Calculus.Deriv.ZPow

namespace Commons.Analysis.Real

/-- First derivative of `r ↦ (r^n)⁻¹`, valid for all `r` (with the convention `deriv = 0`
where the function is not differentiable, which is exactly what the right-hand side gives
at `r = 0`). -/
theorem deriv_inv_pow (n : ℕ) (r : ℝ) :
    deriv (fun s : ℝ => (s ^ n)⁻¹) r = -((n : ℝ) * (r ^ (n + 1))⁻¹) := by
  -- Rewrite `(s ^ n)⁻¹` as the integer power `s ^ (-(n : ℤ))`, which agrees everywhere
  -- (both sides are `0` at `s = 0` when `n > 0`, and `1` when `n = 0`).
  have hfun : (fun s : ℝ => (s ^ n)⁻¹) = fun s : ℝ => s ^ (-(n : ℤ)) := by
    funext s
    rw [zpow_neg, zpow_natCast]
  rw [hfun, deriv_zpow]
  have h1 : (-(n : ℤ) - 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h1, zpow_neg, zpow_natCast]
  push_cast
  ring

end Commons.Analysis.Real