import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Exponential

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Gaussian decay comparison `r e^{-r²/4t} ≤ 2√t e^{-r²/8t}`

For `t > 0` the linear factor `r` is dominated by the *slower* Gaussian
`exp (r²/(8t))`, which together with `exp (-(r²/(4t))) = exp (-(r²/(8t))) · exp (-(r²/(8t)))`
yields the elementary estimate
`r * exp (-(r²/(4t))) ≤ 2 √t * exp (-(r²/(8t)))`.

The only analytic input is `Real.add_one_le_exp` (`1 + x ≤ exp x`); the rest is the
elementary quadratic inequality `r² - 4√t r + 8t = (r - 2√t)² + 4t ≥ 0`.
-/

set_option linter.unusedVariables false

namespace Work.FTS.PressureOn.Auxiliary

theorem ihak_r_exp_gauss_le (t r : ℝ) (ht : 0 < t) (hr : 0 ≤ r) :
    r * Real.exp (-(r ^ 2 / (4 * t))) ≤ 2 * Real.sqrt t * Real.exp (-(r ^ 2 / (8 * t))) := by
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
  have h4s : (0 : ℝ) < 4 * Real.sqrt t := by positivity
  -- `r ≤ 2√t e^{r²/8t}`: it suffices to bound the exponential below by its first
  -- Taylor polynomial, `e^{u} ≥ 1 + u`, and compare quadratics.
  have hpoly : r - 2 * Real.sqrt t ≤ r ^ 2 / (4 * Real.sqrt t) := by
    rw [le_div_iff₀ h4s]
    nlinarith [sq_nonneg (r - 2 * Real.sqrt t), hs2, ht]
  have hexp : 1 + r ^ 2 / (8 * t) ≤ Real.exp (r ^ 2 / (8 * t)) := by
    have h := Real.add_one_le_exp (r ^ 2 / (8 * t))
    linarith
  have h2 : 2 * Real.sqrt t * (1 + r ^ 2 / (8 * t))
      = 2 * Real.sqrt t + r ^ 2 / (4 * Real.sqrt t) := by
    field_simp
    rw [hs2]
    ring
  have h1 : r ≤ 2 * Real.sqrt t * Real.exp (r ^ 2 / (8 * t)) := by
    calc r = (r - 2 * Real.sqrt t) + 2 * Real.sqrt t := by ring
      _ ≤ r ^ 2 / (4 * Real.sqrt t) + 2 * Real.sqrt t := by linarith [hpoly]
      _ = 2 * Real.sqrt t * (1 + r ^ 2 / (8 * t)) := by rw [h2]; ring
      _ ≤ 2 * Real.sqrt t * Real.exp (r ^ 2 / (8 * t)) := by
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
  -- multiply `h1` by `exp (-(r²/4t)) = exp (-(r²/8t)) · exp (-(r²/8t))`
  have harg : r ^ 2 / (8 * t) + -(r ^ 2 / (4 * t)) = -(r ^ 2 / (8 * t)) := by
    field_simp
    ring
  calc r * Real.exp (-(r ^ 2 / (4 * t)))
      ≤ (2 * Real.sqrt t * Real.exp (r ^ 2 / (8 * t))) * Real.exp (-(r ^ 2 / (4 * t))) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = 2 * Real.sqrt t * (Real.exp (r ^ 2 / (8 * t)) * Real.exp (-(r ^ 2 / (4 * t)))) := by ring
    _ = 2 * Real.sqrt t * Real.exp (-(r ^ 2 / (8 * t))) := by
          rw [← Real.exp_add, harg]

end Work.FTS.PressureOn.Auxiliary
