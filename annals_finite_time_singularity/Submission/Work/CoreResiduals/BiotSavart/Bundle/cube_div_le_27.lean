import Mathlib.Algebra.Order.Star.Real
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

/-- **The `27 = (3δ/δ)³` bound.**  For `0 < δ` and `0 ≤ s ≤ δ`,
`(2δ + s)³/(2δ - s)³ ≤ 27`, because `2δ + s ≤ 3δ` and `2δ - s ≥ δ > 0`. -/
theorem cube_div_le_27 {δ s : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hsδ : s ≤ δ) :
    (2 * δ + s) ^ 3 / (2 * δ - s) ^ 3 ≤ 27 := by
  have hpos : 0 < 2 * δ - s := by linarith
  have hcube : 0 < (2 * δ - s) ^ 3 := by positivity
  rw [div_le_iff₀ hcube]
  nlinarith [sq_nonneg (2 * δ - s), sq_nonneg (2 * δ + s), sq_nonneg (s - δ),
    sq_nonneg (2 * δ + s - 3 * (2 * δ - s))]

end Work.CoreResiduals.BiotSavart.Bundle
