import Mathlib
import Submission.Work.Pert.image_cover_mvt
import Submission.Work.Pert.ball_quarter_subset_image_of_lipschitz

namespace Work.Pert

open Metric Set

/-!
# PERT: `ball (Φ z₀) (r/4) ⊆ Φ '' closedBall z₀ r`

A map `Φ` holomorphic on the closed ball `closedBall z₀ r` whose derivative is within `1/2` of `1`
there covers a quarter ball of radius `r/4` around the *image of the centre* `Φ z₀` — no
hypothesis on `‖Φ z₀ - z₀‖` is needed, because the displacement is measured from the centre.

Proof: centre everything at `z₀` by setting `F u = (Φ (z₀+u) - (z₀+u)) - (Φ z₀ - z₀)`, so that
`Φ (z₀+u) - Φ z₀ = u + F u`.  The mean value inequality (`Work.Pert.image_cover_mvt`) gives
`‖F u‖ ≤ ‖u‖/2` on the closed ball; hence `ball 0 (r/4) ⊆ (u ↦ u + F u) '' ball 0 r`
(`Work.Pert.ball_quarter_subset_image_of_lipschitz`, Rouché).  A point `w` with
`‖w - Φ z₀‖ < r/4` is then `Φ (z₀+u) - Φ z₀` for some `‖u‖ < r`, i.e. `w = Φ (z₀+u)` with
`z₀ + u ∈ closedBall z₀ r`.
-/

noncomputable section

theorem image_cover_centered {Φ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ Φ ζ)
    (hder : ∀ ζ ∈ Metric.closedBall z₀ r, ‖deriv Φ ζ - 1‖ ≤ 1 / 2) :
    Metric.ball (Φ z₀) (r / 4) ⊆ Φ '' Metric.closedBall z₀ r := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  -- mean value estimate for the displacement, measured from `z₀`
  have hmvt : ∀ y ∈ Metric.closedBall z₀ r,
      ‖(Φ y - y) - (Φ z₀ - z₀)‖ ≤ (1 / 2) * ‖y - z₀‖ :=
    image_cover_mvt hr hdiff hder
  -- the displacement of `Φ` from the (affinely) centred identity `z ↦ Φ z₀ + (z - z₀)`
  set F : ℂ → ℂ := fun u => (Φ (z₀ + u) - (z₀ + u)) - (Φ z₀ - z₀) with hFdef
  have hFdiff : DifferentiableOn ℂ F (Metric.closedBall (0 : ℂ) r) := by
    have hΦon : DifferentiableOn ℂ Φ (Metric.closedBall z₀ r) :=
      fun x hx => (hdiff x hx).differentiableWithinAt
    have hshift : DifferentiableOn ℂ (fun u : ℂ => z₀ + u) (Metric.closedBall (0 : ℂ) r) :=
      differentiableOn_id.const_add z₀
    have hmaps : Set.MapsTo (fun u : ℂ => z₀ + u)
        (Metric.closedBall (0 : ℂ) r) (Metric.closedBall z₀ r) := by
      intro u hu
      rw [Metric.mem_closedBall] at hu ⊢
      simpa using hu
    have hcomp : DifferentiableOn ℂ (fun u : ℂ => Φ (z₀ + u))
        (Metric.closedBall (0 : ℂ) r) :=
      hΦon.comp hshift hmaps
    have := (hcomp.sub hshift).sub_const (Φ z₀ - z₀)
    simpa [hFdef] using this
  -- on the boundary circle the displacement is at most half the radius
  have hlip : ∀ u ∈ Metric.sphere (0 : ℂ) r, ‖F u‖ ≤ r / 2 := by
    intro u hu
    have hun : ‖u‖ = r := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu
      exact hu
    have hzu : z₀ + u ∈ Metric.closedBall z₀ r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hun]
    have h1 := hmvt (z₀ + u) hzu
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
