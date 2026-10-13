import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.norm_angularVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The inner product of two angular vectors `r e_θ` is bounded by the product of the distances
of the two points to the symmetry axis: this is Cauchy--Schwarz together with
`‖r e_θ‖ = r` (`norm_angularVec`). -/
theorem abs_inner_angularVec_le (x y : Work.Cyl.R3) :
    |inner ℝ (Work.Cyl.angularVec x) (Work.Cyl.angularVec y)|
      ≤ Work.Cyl.radial x * Work.Cyl.radial y := by
  have h := abs_real_inner_le_norm (angularVec x) (angularVec y)
  rwa [norm_angularVec x, norm_angularVec y] at h

end Work.Cyl
