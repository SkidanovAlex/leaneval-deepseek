import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.RCLike.Basic

namespace Commons.Analysis.Real

/-- First derivative of `r ↦ (r^n)⁻¹`, valid for all `r` (with the convention `deriv = 0`
where the function is not differentiable, which is exactly what the right-hand side gives
at `r = 0`).  Private helper: kept local to avoid clashing with the standalone commons
lemma of the same mathematical content. -/
private theorem deriv_inv_pow_aux (n : ℕ) (r : ℝ) :
    deriv (fun s : ℝ => (s ^ n)⁻¹) r = -((n : ℝ) * (r ^ (n + 1))⁻¹) := by
  have hfun : (fun s : ℝ => (s ^ n)⁻¹) = fun s : ℝ => s ^ (-(n : ℤ)) := by
    funext s
    rw [zpow_neg, zpow_natCast]
  rw [hfun, deriv_zpow]
  have h1 : (-(n : ℤ) - 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h1, zpow_neg, zpow_natCast]
  push_cast
  ring

/-- Second derivative of `r ↦ (r^n)⁻¹`, valid for all `r` (with the convention `deriv = 0`
where the function is not differentiable, which is what the right-hand side gives at `r = 0`). -/
theorem deriv_deriv_inv_pow (n : ℕ) (r : ℝ) :
    deriv (deriv (fun s : ℝ => (s ^ n)⁻¹)) r = (n : ℝ) * (n + 1) * (r ^ (n + 2))⁻¹ := by
  -- First derivative, as a function.
  have hderiv : deriv (fun s : ℝ => (s ^ n)⁻¹)
      = fun s : ℝ => (-(n : ℝ)) * (s ^ (n + 1))⁻¹ := by
    funext s
    rw [deriv_inv_pow_aux]
    ring
  rw [hderiv, deriv_const_mul_field, deriv_inv_pow_aux (n + 1)]
  have hpow : (n + 1 + 1 : ℕ) = n + 2 := by ring
  rw [hpow]
  push_cast
  ring

end Commons.Analysis.Real