import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

/-- The operator norm of the continuous linear map `v ↦ u × v` is at most `‖u‖`.

This is the vector identity `‖u × v‖ = ‖u‖ ‖v‖ sin θ ≤ ‖u‖ ‖v‖` fed into the operator-norm
characterization `‖f‖ ≤ M ↔ ∀ v, ‖f v‖ ≤ M ‖v‖`. -/
theorem norm_crossL_le (u : Work.LWP.R3) : ‖Work.StabilityFar.Decay.crossL u‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (crossL u) (norm_nonneg _) (fun v => ?_)
  rw [crossL_apply, InnerProductGeometry.norm_ofLp_crossProduct]
  exact mul_le_of_le_one_right (by positivity) (Real.sin_le_one _)

end Work.StabilityFar.Decay
