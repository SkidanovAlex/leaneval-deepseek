import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.radial_sq_sub_coord_le_dist_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- `reflZ` is the reflection of the axial coordinate, hence an isometry: it preserves distances
(of course even with equality). -/
theorem dist_reflZ_le (x y : Work.Cyl.R3) : dist (Work.Cyl.reflZ x) (Work.Cyl.reflZ y) ≤ dist x y := by
  have hsq : dist (reflZ x) (reflZ y) ^ 2 = dist x y ^ 2 := by
    rw [dist_sq_coords, dist_sq_coords]
    simp [reflZ]
    ring
  have h : dist (reflZ x) (reflZ y) = dist x y := by
    nlinarith [dist_nonneg (x := reflZ x) (y := reflZ y), dist_nonneg (x := x) (y := y)]
  rw [h]

end Work.Cyl
