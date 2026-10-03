import Mathlib
import Submission.Work.Pert.image_cover_mvt
import Submission.Work.Pert.RoucheBridge
import Submission.Work.Repel.covering_near_id

namespace Work.Pert

open Metric Set

/-- Covering for a map `u ↦ u + F u` whose perturbation `F` is bounded by `R/2` on the boundary
circle of radius `R`: it covers the *half*-disc `ball 0 (R/2)`.  This is the sharp form of
`Work.Pert.ball_quarter_subset_image_of_lipschitz` (same Rouché argument: on the sphere
`‖F z - w‖ ≤ ‖F z‖ + ‖w‖ < R/2 + R/2 = R = ‖z‖` as soon as `‖w‖ < R/2`). -/
theorem ball_half_subset_image_of_lipschitz {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.closedBall (0 : ℂ) R))
    (hlip : ∀ u ∈ Metric.sphere (0 : ℂ) R, ‖F u‖ ≤ R / 2) :
    Metric.ball (0 : ℂ) (R / 2) ⊆ (fun u : ℂ => u + F u) '' Metric.ball (0 : ℂ) R := by
  intro w hw
  have hwlt : ‖w‖ < R / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  -- Rouché's hypothesis on the boundary sphere
  have hlt : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖F z - w‖ < ‖(fun u : ℂ => u) z‖ := by
    intro z hz
    show ‖F z - w‖ < ‖z‖
    have hzR : ‖z‖ = R := by simpa using hz
    calc ‖F z - w‖ ≤ ‖F z‖ + ‖w‖ := norm_sub_le _ _
      _ < R / 2 + R / 2 := by linarith [hlip z hz]
      _ = R := by ring
      _ = ‖z‖ := hzR.symm
  -- Rouché with `f = id`, `g = F - w`, `a = 0`: `id + g = fun u => u + F u - w` has a zero `z`
  -- in the disc, i.e. `z + F z = w`.
  obtain ⟨z, hz, hz0, -⟩ :=
    Commons.Analysis.Complex.rouche_simple_zero (R := R) hR (f := fun u : ℂ => u)
      (g := fun u : ℂ => F u - w) (a := 0)
      (by simpa using hR) differentiableOn_id continuousOn_id
      (hF.sub (differentiableOn_const w))
      (hF.continuousOn.sub continuousOn_const)
      hlt (by simp) (by simp) (fun z _ h0 => h0)
  exact ⟨z, hz, by linear_combination hz0⟩

theorem cover_half_centered {Φ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ Φ ζ)
    (hder : ∀ ζ ∈ Metric.closedBall z₀ r, ‖deriv Φ ζ - 1‖ ≤ 1 / 2) :
    Metric.ball (Φ z₀) (r / 2) ⊆ Φ '' Metric.closedBall z₀ r := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  -- mean value estimate for the displacement, measured from `z₀`
  have hmvt : ∀ y ∈ Metric.closedBall z₀ r,
      ‖(Φ y - y) - (Φ z₀ - z₀)‖ ≤ (1 / 2) * ‖y - z₀‖ :=
    image_cover_mvt hr hdiff hder
  -- the displacement of `Φ` from the affinely centred identity `z ↦ Φ z₀ + (z - z₀)`
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
  have hcov := ball_half_subset_image_of_lipschitz hr hFdiff hlip
  have hv : w - Φ z₀ ∈ Metric.ball (0 : ℂ) (r / 2) := by
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

end Work.Pert
