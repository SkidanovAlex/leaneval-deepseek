import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The squared distance in coordinates: `‖x - y‖²` is the sum of the squares of the coordinate
differences. -/
lemma dist_sq_coords (x y : R3) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_three, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

theorem radial_sq_sub_coord_le_dist_sq (x y : Work.Cyl.R3) :
    Work.Cyl.radial x ^ 2 + Work.Cyl.radial y ^ 2 - 2 * (x 0 * y 0 + x 1 * y 1)
      ≤ dist x y ^ 2 := by
  have hx : radial x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by rw [radial_sq, radSq]
  have hy : radial y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by rw [radial_sq, radSq]
  rw [hx, hy, dist_sq_coords]
  nlinarith [sq_nonneg (x 2 - y 2)]

end Work.Cyl
