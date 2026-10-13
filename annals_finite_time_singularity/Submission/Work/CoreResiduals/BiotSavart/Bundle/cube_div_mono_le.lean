import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

/-- **Monotonicity of `t ↦ (ρ+t)³/(ρ-t)³` on `[0,ρ)`.**  If `0 ≤ R' < ρ` and `‖x‖ ≤ R'` then
`(ρ + ‖x‖)³/(ρ - ‖x‖)³ ≤ (ρ + R')³/(ρ - R')³`: the numerator grows and the (positive)
denominator shrinks as `t` increases. -/
theorem cube_div_mono_le {ρ R' : ℝ} (hR' : 0 ≤ R') (hρ : R' < ρ) {x : Work.LWP.R3}
    (hx : ‖x‖ ≤ R') :
    (ρ + ‖x‖) ^ 3 / (ρ - ‖x‖) ^ 3 ≤ (ρ + R') ^ 3 / (ρ - R') ^ 3 := by
  have ht : 0 ≤ ‖x‖ := norm_nonneg x
  have hρpos : 0 < ρ := lt_of_le_of_lt hR' hρ
  have hb : 0 < ρ - ‖x‖ := by linarith
  have hd : 0 < ρ - R' := by linarith
  have hnum : 0 ≤ ρ + ‖x‖ := by linarith
  have hg : (ρ + ‖x‖) / (ρ - ‖x‖) ≤ (ρ + R') / (ρ - R') := by
    rw [div_le_div_iff₀ hb hd]
    nlinarith
  rw [← div_pow, ← div_pow]
  exact pow_le_pow_left₀ (div_nonneg hnum (le_of_lt hb)) hg 3

end Work.CoreResiduals.BiotSavart.Bundle
