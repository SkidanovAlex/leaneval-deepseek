import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The angular vector `angularVec x = (-x₁, x₀, 0) = r e_θ` is orthogonal to the axis, so the
inner product of two angular vectors is the inner product of their projections onto the
`(x₀,x₁)`-plane. -/
theorem inner_angularVec (x y : Work.Cyl.R3) :
    inner ℝ (Work.Cyl.angularVec x) (Work.Cyl.angularVec y) = x 0 * y 0 + x 1 * y 1 := by
  rw [inner_eq]
  simp
  ring

end Work.Cyl
