import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Construction.GammaTermAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

/-- Elementary numerical bounds for the surviving radial profile coefficients:
each of the five polynomials is dominated by `840 * (1 + z)^k` on `z ≥ 0`. -/
theorem H4N_rhoR_numbound :
    (∀ z : ℝ, 0 ≤ z → |(1:ℝ)| ≤ 840 * (1 + z)^0)
    ∧ (∀ z : ℝ, 0 ≤ z → |2 - 2*z| ≤ 840 * (1 + z)^1)
    ∧ (∀ z : ℝ, 0 ≤ z → |4 - 12*z + 4*z^2| ≤ 840 * (1 + z)^2)
    ∧ (∀ z : ℝ, 0 ≤ z → |8 - 52*z + 52*z^2 - 8*z^3| ≤ 840 * (1 + z)^3)
    ∧ (∀ z : ℝ, 0 ≤ z → |16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4| ≤ 840 * (1 + z)^4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z _
    norm_num
  · intro z _
    rw [abs_le]
    constructor <;> nlinarith
  · intro z _
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z]
  · intro z hz
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z, mul_nonneg hz (sq_nonneg z)]
  · intro z hz
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg z, mul_nonneg hz (sq_nonneg z), sq_nonneg (z^2)]

end Work.Construction
