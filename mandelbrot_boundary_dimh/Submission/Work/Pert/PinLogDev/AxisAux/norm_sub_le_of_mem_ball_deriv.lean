import Mathlib

namespace Work.Pert.PinLogDev.AxisAux

theorem norm_sub_le_of_mem_ball_deriv {u : ℂ → ℂ} {rr : ℝ} (hrr : 0 < rr)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) rr, ‖u z‖ ≤ 2)
    (h0 : ‖u 0 - 1‖ ≤ 1 / 8)
    {τ : ℂ} (hτ : τ ∈ Metric.ball (0 : ℂ) rr) :
    ‖u τ - u 0‖ ≤ (4 / rr) * ‖τ‖ := by
  -- `u` is bounded by `2` on the ball, and `u 0` is within `1/8` of `1`,
  -- hence `‖u 0‖ ≤ 9/8`.
  have hc : ‖u 0‖ ≤ 9 / 8 := by
    have h1 : ‖u 0‖ ≤ ‖u 0 - 1‖ + ‖(1 : ℂ)‖ := by
      have := norm_add_le (u 0 - 1) (1 : ℂ)
      rwa [sub_add_cancel] at this
    simp only [norm_one] at h1
    linarith
  -- Therefore `u` maps the ball of radius `rr` into the closed ball of radius
  -- `25/8` centered at `u 0`.
  have hmaps : Set.MapsTo u (Metric.ball (0 : ℂ) rr) (Metric.closedBall (u 0) (25 / 8)) := by
    intro z hz
    rw [Metric.mem_closedBall]
    calc dist (u z) (u 0) ≤ dist (u z) 0 + dist 0 (u 0) := dist_triangle _ _ _
      _ = ‖u z‖ + ‖u 0‖ := by simp [dist_eq_norm]
      _ ≤ 2 + 9 / 8 := add_le_add (hb z hz) hc
      _ = 25 / 8 := by norm_num
  -- Schwarz–Pick (`Complex.dist_le_div_mul_dist_of_mapsTo_ball`) at `c = 0`.
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hu hmaps hτ
  rw [dist_eq_norm, dist_eq_norm, sub_zero] at hsch
  calc ‖u τ - u 0‖ ≤ (25 / 8) / rr * ‖τ‖ := hsch
    _ = (25 / (8 * rr)) * ‖τ‖ := by ring
    _ ≤ (4 / rr) * ‖τ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg τ)
        have key : (25 : ℝ) / (8 * rr) = (25 / 8) / rr := by ring
        rw [key, div_le_div_iff_of_pos_right hrr]
        norm_num

end Work.Pert.PinLogDev.AxisAux
