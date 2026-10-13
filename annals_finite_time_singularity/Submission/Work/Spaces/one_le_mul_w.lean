import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- The radial weight beats the reciprocal of `z`: `1 ≤ z · w(z)` for `z > 0`, because
`z·w(z) = (1+z)²/z = z + 2 + 1/z ≥ 1`. -/
theorem one_le_mul_w (z : ℝ) (hz : 0 < z) : 1 ≤ z * Work.Spaces.w z := by
  have hzw : z * Work.Spaces.w z = (1 + z) ^ 2 / z := by
    rw [Work.Spaces.w]
    field_simp
  rw [hzw, le_div_iff₀ hz]
  nlinarith [sq_nonneg z]

end Work.Spaces
