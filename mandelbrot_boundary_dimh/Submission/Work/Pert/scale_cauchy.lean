import Mathlib

namespace Work.Pert

/-- Cauchy estimate at a shifted centre.

If `u : ℂ → ℂ` is holomorphic on the ball `ball 0 ρ` and bounded by `2` there, then
for every `z` with `‖z‖ ≤ ρmin / 2` (where `ρmin ≤ ρ`) the derivative at `z` is bounded by
`8 / ρmin`.  The proof is the Schwarz/Cauchy estimate on the ball of radius `ρmin / 2`
centred at `z`, which lies inside `ball 0 ρ`; the values of `u` on that ball lie in the
closed ball of radius `4` around `u z`. -/
theorem deriv_bound {u : ℂ → ℂ} {ρ ρmin : ℝ} (hρmin : 0 < ρmin) (hρ : ρmin ≤ ρ)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ))
    (hub : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖u z‖ ≤ 2) :
    ∀ z : ℂ, ‖z‖ ≤ ρmin / 2 → ‖deriv u z‖ ≤ 8 / ρmin := by
  intro z hz
  -- the small ball around `z` sits inside the big ball
  have hsubz : Metric.ball z (ρmin / 2) ⊆ Metric.ball (0 : ℂ) ρ := fun w hw => by
    have hw' : dist w z < ρmin / 2 := by simpa [Metric.mem_ball] using hw
    have hz2 : dist z 0 ≤ ρmin / 2 := by
      rw [dist_eq_norm, sub_zero]; exact hz
    rw [Metric.mem_ball]
    calc dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
      _ < ρmin / 2 + ρmin / 2 := add_lt_add_of_lt_of_le hw' hz2
      _ = ρmin := by ring
      _ ≤ ρ := hρ
  have hzρ : z ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hd : DifferentiableOn ℂ u (Metric.ball z (ρmin / 2)) := hu.mono hsubz
  have hmaps : Set.MapsTo u (Metric.ball z (ρmin / 2)) (Metric.closedBall (u z) 4) := by
    intro w hw
    rw [Metric.mem_closedBall]
    calc dist (u w) (u z) ≤ dist (u w) 0 + dist 0 (u z) := dist_triangle (u w) 0 (u z)
      _ = ‖u w‖ + ‖u z‖ := by rw [dist_zero_right, dist_zero_left]
      _ ≤ 2 + 2 := add_le_add (hub w (hsubz hw)) (hub z hzρ)
      _ = 4 := by norm_num
  have h := Complex.norm_deriv_le_div_of_mapsTo_ball hd hmaps (by linarith : (0:ℝ) < ρmin / 2)
  calc ‖deriv u z‖ ≤ 4 / (ρmin / 2) := h
    _ = 8 / ρmin := by rw [div_div_eq_mul_div]; norm_num

theorem scale_cauchy {u : ℂ → ℂ} {ρ ρmin : ℝ} (hρmin : 0 < ρmin) (hρ : ρmin ≤ ρ)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ))
    (hub : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖u z‖ ≤ 2) :
    (∀ z : ℂ, ‖z‖ ≤ ρmin / 2 → ‖deriv u z‖ ≤ 8 / ρmin) ∧
    (∀ τ : ℂ, ‖τ‖ ≤ ρmin / 2 → ‖u 0 - u τ‖ ≤ (8 / ρmin) * ‖τ‖) := by
  refine ⟨deriv_bound hρmin hρ hu hub, fun τ hτ => ?_⟩
  have hx : τ ∈ Metric.closedBall (0 : ℂ) (ρmin / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hτ
  have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (ρmin / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact le_of_lt (half_pos hρmin)
  have hdiff : ∀ x ∈ Metric.closedBall (0 : ℂ) (ρmin / 2), DifferentiableAt ℂ u x := by
    intro x hx'
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    have hxρ : x ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    exact hu.differentiableAt (Metric.isOpen_ball.mem_nhds hxρ)
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) (ρmin / 2), ‖deriv u x‖ ≤ 8 / ρmin := by
    intro x hx'
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    exact deriv_bound hρmin hρ hu hub x hx'
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_closedBall (0 : ℂ) (ρmin / 2)) h0 hx
  rwa [sub_zero, norm_sub_rev] at hmvt

end Work.Pert
