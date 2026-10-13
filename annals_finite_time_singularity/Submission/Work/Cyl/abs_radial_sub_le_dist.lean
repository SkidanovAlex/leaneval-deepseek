import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `r` is 1-Lipschitz: `|r x - r y| ≤ dist x y`

The distance `radial x = √(x₀² + x₁²)` to the axis is the norm of the "radial vector"
`radialVec x = (x₀, x₁, 0)`, and the map `x ↦ radialVec x` does not increase distances (it
forgets the coordinate `x₂`).  Composing the reverse triangle inequality for the norm with this
observation gives the claim.
-/

namespace Work.Cyl

/-- The radial coordinate is the norm of the radial vector `r e_r = (x₀, x₁, 0)`. -/
lemma radial_eq_norm_radialVec' (x : R3) : radial x = ‖radialVec x‖ := by
  have h : radSq x = ‖radialVec x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_radialVec_self]
  rw [radial, h, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The map `x ↦ (x₀, x₁, 0)` does not increase distances: it is the orthogonal projection onto
the plane spanned by the first two coordinates. -/
lemma norm_radialVec_sub_le_dist (x y : R3) : ‖radialVec x - radialVec y‖ ≤ ‖x - y‖ := by
  have h : ‖radialVec x - radialVec y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_eq, inner_eq]
    simp only [PiLp.sub_apply, radialVec_apply_zero, radialVec_apply_one, radialVec_apply_two]
    nlinarith [sq_nonneg (x 2 - y 2)]
  have := sq_le_sq.mp h
  simpa [abs_of_nonneg (norm_nonneg _)] using this

theorem abs_radial_sub_le_dist (x y : Work.Cyl.R3) :
    |Work.Cyl.radial x - Work.Cyl.radial y| ≤ dist x y := by
  rw [radial_eq_norm_radialVec' x, radial_eq_norm_radialVec' y, dist_eq_norm]
  exact le_trans (abs_norm_sub_norm_le _ _) (norm_radialVec_sub_le_dist x y)

end Work.Cyl
