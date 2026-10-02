import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Area

/-- If `k` is complex differentiable on a disc of radius `R'` and has no zeros on the
closed disc of radius `R < R'`, then the logarithmic derivative `k'/k` integrates to
zero over the circle `|z| = R`.  This is the special case of the argument principle
with no zeros (equivalently, no poles of `k'/k`) inside the contour. -/
theorem circleIntegral_deriv_div_eq_zero {k : ℂ → ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R')
    (hk : DifferentiableOn ℂ k (Metric.ball 0 R'))
    (hne : ∀ w ∈ Metric.closedBall 0 R, k w ≠ 0) :
    circleIntegral (fun w => deriv k w / k w) 0 R = 0 := by
  -- `ball 0 R ⊆ ball 0 R'`
  have hsub : Metric.ball (0 : ℂ) R ⊆ Metric.ball 0 R' := Metric.ball_subset_ball hRR.le
  -- `k` is differentiable on `ball 0 R`, and so is `deriv k` (analyticity)
  have hkR : DifferentiableOn ℂ k (Metric.ball 0 R) := hk.mono hsub
  have hk'_R' : DifferentiableOn ℂ (deriv k) (Metric.ball 0 R') := hk.deriv Metric.isOpen_ball
  have hk'_R : DifferentiableOn ℂ (deriv k) (Metric.ball 0 R) := hk'_R'.mono hsub
  -- `k` does not vanish on `ball 0 R`
  have hneR : ∀ w ∈ Metric.ball 0 R, k w ≠ 0 :=
    fun w hw => hne w (Metric.ball_subset_closedBall hw)
  -- hence `w ↦ deriv k w / k w` is differentiable on `ball 0 R`
  have hd : DifferentiableOn ℂ (fun w => deriv k w / k w) (Metric.ball 0 R) :=
    hk'_R.div hkR hneR
  -- and continuous on the closed disc `closedBall 0 R`
  have hcont_k' : ContinuousOn (deriv k) (Metric.closedBall (0 : ℂ) R) :=
    fun w hw => (((hk'_R'.differentiableAt (Metric.isOpen_ball.mem_nhds
      (Metric.closedBall_subset_ball hRR hw))).continuousAt).continuousWithinAt)
  have hcont_k : ContinuousOn k (Metric.closedBall (0 : ℂ) R) :=
    fun w hw => (((hk.differentiableAt (Metric.isOpen_ball.mem_nhds
      (Metric.closedBall_subset_ball hRR hw))).continuousAt).continuousWithinAt)
  have hc : ContinuousOn (fun w => deriv k w / k w) (Metric.closedBall (0 : ℂ) R) :=
    hcont_k'.div hcont_k hne
  -- Cauchy–Goursat on the disc
  have hg : DiffContOnCl ℂ (fun w => deriv k w / k w) (Metric.ball 0 R) :=
    DiffContOnCl.mk_ball hd hc
  exact DiffContOnCl.circleIntegral_eq_zero hR.le hg

end Work.Area
