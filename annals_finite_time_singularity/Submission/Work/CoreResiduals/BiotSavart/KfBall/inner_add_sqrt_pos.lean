import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.KfBall

/-- For `‖z‖ < ρ` and any `ω` on the unit sphere, the quantity
`⟪z, ω⟫ + √(⟪z, ω⟫² + (ρ² - ‖z‖²))` is strictly positive. -/
theorem inner_add_sqrt_pos (z : Work.LWP.R3) {ρ : ℝ} (hz : ‖z‖ < ρ)
    (ω : Metric.sphere (0 : Work.LWP.R3) 1) :
    0 < inner ℝ z (ω : Work.LWP.R3)
      + Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2)) := by
  set a := inner ℝ z (ω : Work.LWP.R3) with ha
  -- `ρ² - ‖z‖² > 0` because `‖z‖ < ρ` (which forces `ρ > 0`).
  have hb : 0 < ρ ^ 2 - ‖z‖ ^ 2 := by
    have h1 : 0 ≤ ‖z‖ := norm_nonneg z
    have h2 : 0 < ρ := lt_of_le_of_lt h1 hz
    nlinarith
  -- The square root dominates `|a|`.
  have hlt : |a| < Real.sqrt (a ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg a) (by nlinarith)
  -- `-a ≤ |a| < √(...)`, hence `a + √(...) > 0`.
  linarith [neg_le_abs a, hlt]

end Work.CoreResiduals.BiotSavart.KfBall
