import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- `‖r e_θ‖ = r`: the length of the angular vector `angularVec x = (-x₁, x₀, 0)` is the
distance `radial x` of `x` to the symmetry axis. -/
theorem norm_angularVec (x : Work.Cyl.R3) : ‖Work.Cyl.angularVec x‖ = Work.Cyl.radial x := by
  have h : ‖angularVec x‖ ^ 2 = radSq x := by
    rw [← real_inner_self_eq_norm_sq, inner_angularVec_self]
  have h2 : radial x ^ 2 = radSq x := radial_sq x
  nlinarith [norm_nonneg (angularVec x), radial_nonneg x]

end Work.Cyl
