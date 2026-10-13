import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- For `0 < t ≤ 1` and `0 < α < 1` we have `1024 t^2 + 4 t ≤ 1028 t^α`:
both `t^2 ≤ t^α` (as `α ≤ 2` and the base lies in `(0,1]`) and `t ≤ t^α`
(as `α ≤ 1`), and these combine with the coefficients. -/
theorem rpow_sq_le_exp_small {t α : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 < α) (hα1 : α < 1) :
    1024 * t ^ (2 : ℝ) + 4 * t ≤ 1028 * t ^ α := by
  have h2 : t ^ (2 : ℝ) ≤ t ^ α :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have h1 : t ≤ t ^ α := by
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 (le_of_lt hα1)
    rwa [Real.rpow_one] at h
  nlinarith [h1, h2]

end Work.CoreResiduals.BiotSavart
