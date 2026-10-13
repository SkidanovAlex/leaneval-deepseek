import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- For `x ≥ 0`, the square of `x ^ (-(γ/2))` is `x ^ (-γ)`. -/
theorem rpow_neg_sq (x γ : ℝ) (hx : 0 ≤ x) : (x ^ (-(γ / 2))) ^ 2 = x ^ (-γ) := by
  rw [← Real.rpow_natCast (x ^ (-(γ / 2))) 2]
  calc (x ^ (-(γ / 2))) ^ (2 : ℝ)
      = x ^ ((-(γ / 2)) * 2) := (Real.rpow_mul hx (-(γ / 2)) (2 : ℝ)).symm
    _ = x ^ (-γ) := by rw [show (-(γ / 2)) * 2 = -γ by ring]

end Work.Coercivity
