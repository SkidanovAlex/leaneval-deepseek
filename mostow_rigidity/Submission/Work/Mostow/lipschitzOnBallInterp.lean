import Mathlib

namespace Work.Mostow

theorem lipschitzOnBallInterp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (C : ℝ) (hf : ContDiff ℝ 1 f)
    (hC : ∀ x ∈ Metric.closedBall (0 : E) 1, ‖fderiv ℝ f x‖ ≤ C) :
    ∀ x ∈ Metric.closedBall (0 : E) 1, ∀ y ∈ Metric.closedBall (0 : E) 1,
      ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  intro x hx y hy
  -- `f` is differentiable at every point of the closed ball (it is `C¹`).
  have hdiff : ∀ z ∈ Metric.closedBall (0 : E) 1, DifferentiableAt ℝ f z :=
    fun z _ => hf.contDiffAt.differentiableAt_one
  -- Mean value inequality on the convex closed ball, with the two endpoints swapped.
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hC (convex_closedBall 0 1) hy hx

end Work.Mostow
