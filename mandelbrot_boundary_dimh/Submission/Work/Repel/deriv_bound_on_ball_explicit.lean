import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.repel3_aux

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- **Cauchy's estimate with an explicit bound**, uniform on a ball.

If `g` is holomorphic on an open set `U` containing `closedBall c (2R)` and
`‖g‖ ≤ B` on that closed ball, then `‖deriv g z‖ ≤ max B 1 / R` for every
`z ∈ closedBall c R`.  The `max B 1` makes the bound positive unconditionally
(and dominates the compactness bound used in `deriv_bound_on_ball`). -/
theorem deriv_bound_on_ball_explicit {g : ℂ → ℂ} {U : Set ℂ} (hg : DifferentiableOn ℂ g U)
    {c : ℂ} {R B : ℝ} (hR : 0 < R) (hsub : Metric.closedBall c (2 * R) ⊆ U)
    (hB : ∀ z ∈ Metric.closedBall c (2 * R), ‖g z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall c R, ‖deriv g z‖ ≤ max B 1 / R := by
  intro z hz
  -- the disc of radius `R` about `z` lies in `closedBall c (2R)`
  have hmem2 : ∀ w ∈ Metric.closedBall z R, w ∈ Metric.closedBall c (2 * R) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ R + R := by
            have hz' : ‖z - c‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
            linarith
      _ = 2 * R := by ring
  have hmem : ∀ w ∈ Metric.closedBall z R, w ∈ U := fun w hw => hsub (hmem2 w hw)
  have hd : DiffContOnCl ℂ g (Metric.ball z R) := by
    refine ⟨hg.mono (fun w hw => hmem w (Metric.ball_subset_closedBall hw)), ?_⟩
    rw [closure_ball z (ne_of_gt hR)]
    exact (hg.mono hmem).continuousOn
  have hC : ∀ w ∈ Metric.sphere z R, ‖g w‖ ≤ max B 1 := fun w hw =>
    le_trans (hB w (hmem2 w (Metric.sphere_subset_closedBall hw))) (le_max_left _ _)
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := g) (c := z) (R := R) (C := max B 1) hR hd hC

end

end Work.Repel
