import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.image_cover_mvt
import Submission.Work.Pert.differentiableOn_comp_shift
import Submission.Work.Pert.ball_quarter_subset_image_of_lipschitz

/-!
# PERT: the ball `ball (Φ z₀) (r/4)` is covered by `Φ '' closedBall z₀ r`

A map `Φ` holomorphic on an open set `Q ⊇ closedBall z₀ r` whose derivative is within `1/2` of
`1` on that ball and which moves the centre by at most `r/4` is "close enough to the identity"
that its image of the ball covers a full quarter-ball around `Φ z₀`.  This is the elementary
covering estimate used in the PERT area (Shishikura Lemma A.1.4 / (4.2.x)).

Proof: put `F u = (Φ (z₀+u) - (z₀+u)) - (Φ z₀ - z₀)`, the displacement of `Φ` measured from the
centre `Φ z₀` at `z₀`.  The mean value inequality (`Work.Pert.image_cover_mvt`) gives
`‖F u‖ ≤ ‖u‖/2` on the closed ball, and

`Φ (z₀+u) - Φ z₀ = u + F u`,

so it suffices to know that `u ↦ u + F u` covers the quarter-ball.  That is
`Work.Pert.ball_quarter_subset_image_of_lipschitz`, whose proof is Rouché's theorem applied to
`id` and `u ↦ F u - w` on the disc of radius `r` (`‖F u - w‖ ≤ r/2 + r/4 < r = ‖u‖` on the
sphere).
-/

namespace Work.Pert

open Metric Set

noncomputable section

theorem image_cover {Q : Set ℂ} {Φ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hQ : IsOpen Q) (hsub : Metric.closedBall z₀ r ⊆ Q)
    (hΦ : DifferentiableOn ℂ Φ Q)
    (hder : ∀ ζ ∈ Metric.closedBall z₀ r, ‖deriv Φ ζ - 1‖ ≤ 1 / 2)
    (hanchor : ‖Φ z₀ - z₀‖ ≤ r / 4) :
    Metric.ball (Φ z₀) (r / 4) ⊆ Φ '' Metric.closedBall z₀ r := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  -- `Φ` is differentiable at every point of the closed ball, `Q` being open
  have hdiffAt : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ Φ ζ := by
    intro ζ hζ
    exact hΦ.differentiableAt (hQ.mem_nhds (hsub hζ))
  -- mean value estimate for the displacement, measured from `z₀`
  have hmvt : ∀ y ∈ Metric.closedBall z₀ r,
      ‖(Φ y - y) - (Φ z₀ - z₀)‖ ≤ (1 / 2) * ‖y - z₀‖ :=
    image_cover_mvt hr hdiffAt hder
  -- the shifted composition is differentiable on the closed ball
  have hshift : DifferentiableOn ℂ (fun u : ℂ => Φ (z₀ + u)) (Metric.closedBall (0 : ℂ) r) :=
    differentiableOn_comp_shift hQ hsub hΦ
  set F : ℂ → ℂ := fun u => (Φ (z₀ + u) - (z₀ + u)) - (Φ z₀ - z₀) with hFdef
  have hFdiff : DifferentiableOn ℂ F (Metric.closedBall (0 : ℂ) r) := by
    rw [hFdef]
    exact (hshift.sub (differentiableOn_id.const_add z₀)).sub_const (Φ z₀ - z₀)
  -- on the boundary circle the displacement is at most half the radius
  have hlip : ∀ u ∈ Metric.sphere (0 : ℂ) r, ‖F u‖ ≤ r / 2 := by
    intro u hu
    have hun : ‖u‖ = r := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu
      exact hu
    have hu' : z₀ + u ∈ Metric.closedBall z₀ r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hun]
    have h1 := hmvt (z₀ + u) hu'
    rw [hFdef]
    rw [add_sub_cancel_left, hun] at h1
    linarith
  -- the covering statement for `u ↦ u + F u`
  have hcov := ball_quarter_subset_image_of_lipschitz hr hFdiff hlip
  have hv : w - Φ z₀ ∈ Metric.ball (0 : ℂ) (r / 4) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hw
  obtain ⟨u, hu_ball, hu_eq⟩ := hcov hv
  have hu_norm : ‖u‖ < r := by
    rwa [Metric.mem_ball, dist_zero_right] at hu_ball
  refine ⟨z₀ + u, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact le_of_lt hu_norm
  · -- `u + F u = Φ (z₀+u) - Φ z₀ = w - Φ z₀`
    rw [hFdef] at hu_eq
    linear_combination hu_eq

end

end Work.Pert
