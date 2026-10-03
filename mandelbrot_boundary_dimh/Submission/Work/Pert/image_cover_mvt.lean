import Mathlib

namespace Work.Pert

open Metric

/-- Mean value (Lipschitz) estimate for the displacement `Φ - id` of a map whose derivative is
within `1/2` of `1` on the closed ball `closedBall z₀ r`.  Apply
`Convex.norm_image_sub_le_of_norm_deriv_le` on the segment `[z₀, y]` (contained in the convex
closed ball) to `z ↦ Φ z - z`, whose derivative is `deriv Φ z - 1`. -/
theorem image_cover_mvt {Φ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ Φ ζ)
    (hb : ∀ ζ ∈ Metric.closedBall z₀ r, ‖deriv Φ ζ - 1‖ ≤ 1 / 2) :
    ∀ y ∈ Metric.closedBall z₀ r,
      ‖(Φ y - y) - (Φ z₀ - z₀)‖ ≤ (1 / 2) * ‖y - z₀‖ := by
  intro y hy
  -- the closed ball is convex and contains its centre
  have hz0 : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  -- the displacement `z ↦ Φ z - z` is differentiable on the ball
  have hf : ∀ x ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ (fun z : ℂ => Φ z - z) x :=
    fun x hx => (hdiff x hx).sub differentiableAt_id
  -- and its derivative is `deriv Φ x - 1`, bounded by `1/2`
  have hbound : ∀ x ∈ Metric.closedBall z₀ r, ‖deriv (fun z : ℂ => Φ z - z) x‖ ≤ 1 / 2 := by
    intro x hx
    have h1 : deriv (fun z : ℂ => Φ z - z) x = deriv Φ x - 1 := by
      rw [show (fun z : ℂ => Φ z - z) = Φ - id from rfl,
        deriv_sub (hdiff x hx) differentiableAt_id, deriv_id]
    rw [h1]
    exact hb x hx
  exact Convex.norm_image_sub_le_of_norm_deriv_le hf hbound (convex_closedBall z₀ r) hz0 hy

end Work.Pert
