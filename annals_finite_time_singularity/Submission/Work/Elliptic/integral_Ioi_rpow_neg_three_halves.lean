import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- For `z > 0`, the improper integral of `t ↦ t^{-3/2}` over `(z, ∞)` equals
`2 z^{-1/2}`. -/
theorem integral_Ioi_rpow_neg_three_halves (z : ℝ) (hz : 0 < z) :
    ∫ t in Set.Ioi z, t ^ (-(3/2:ℝ)) = 2 * z ^ (-(1/2:ℝ)) := by
  rw [integral_Ioi_rpow_of_lt (a := -(3/2:ℝ)) (by norm_num) hz]
  norm_num
  ring

end Work.Elliptic
