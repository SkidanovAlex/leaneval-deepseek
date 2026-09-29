import Mathlib

namespace Work.C17g

theorem local_lipschitz_holo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set ℂ} (hSo : IsOpen S) {f : ℂ → E} (hf : DifferentiableOn ℂ f S)
    {T : Set ℂ} {ρ B : ℝ} (hρ : 0 < ρ) (hTS : Metric.cthickening ρ T ⊆ S)
    (hB : ∀ z ∈ Metric.cthickening ρ T, ‖f z‖ ≤ B) :
    ∀ x ∈ T, ∀ y ∈ T, ‖y - x‖ < ρ / 2 → ‖f y - f x‖ ≤ (2 * B / ρ) * ‖y - x‖ := by
  intro x hxT y hyT hxy
  have hB0 : 0 ≤ B := by
    have hxc : x ∈ Metric.cthickening ρ T :=
      Metric.mem_cthickening_of_dist_le x x ρ T hxT (by simpa using hρ.le)
    exact le_trans (norm_nonneg _) (hB x hxc)
  have hρ2pos : 0 < ρ / 2 := by linarith
  -- Cauchy estimate at every point of the radius-`ρ/2` disc around `x`
  have hderiv : ∀ z ∈ Metric.ball x (ρ / 2), ‖deriv f z‖ ≤ 2 * B / ρ := by
    intro z hz
    rw [Metric.mem_ball] at hz
    have hzx : ‖z - x‖ < ρ / 2 := by simpa [dist_eq_norm] using hz
    set r : ℝ := ρ - ‖z - x‖ with hr
    have hrpos : 0 < r := by rw [hr]; linarith
    have hsphere : ∀ w ∈ Metric.sphere z r, ‖f w‖ ≤ B := by
      intro w hw
      rw [Metric.mem_sphere, dist_eq_norm] at hw
      apply hB
      apply Metric.mem_cthickening_of_dist_le w x ρ T hxT
      rw [dist_eq_norm]
      have h1 : w - x = (w - z) + (z - x) := by ring
      calc ‖w - x‖ = ‖(w - z) + (z - x)‖ := by rw [h1]
        _ ≤ ‖w - z‖ + ‖z - x‖ := norm_add_le _ _
        _ = r + ‖z - x‖ := by rw [hw]
        _ = ρ := by rw [hr]; ring
    have hd : DiffContOnCl ℂ f (Metric.ball z r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hrpos.ne']
      apply hf.mono
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      apply hTS
      apply Metric.mem_cthickening_of_dist_le w x ρ T hxT
      rw [dist_eq_norm]
      have h1 : w - x = (w - z) + (z - x) := by ring
      calc ‖w - x‖ = ‖(w - z) + (z - x)‖ := by rw [h1]
        _ ≤ ‖w - z‖ + ‖z - x‖ := norm_add_le _ _
        _ ≤ r + ‖z - x‖ := by linarith
        _ = ρ := by rw [hr]; ring
    have hcauchy : ‖deriv f z‖ ≤ B / r :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hd hsphere
    have hrge : ρ / 2 ≤ r := by rw [hr]; linarith
    have hstep : B / r ≤ B / (ρ / 2) := div_le_div_of_nonneg_left hB0 hρ2pos hrge
    have heq : B / (ρ / 2) = 2 * B / ρ := by
      rw [div_div_eq_mul_div]; ring
    calc ‖deriv f z‖ ≤ B / r := hcauchy
      _ ≤ B / (ρ / 2) := hstep
      _ = 2 * B / ρ := heq
  have hdiff : ∀ z ∈ Metric.ball x (ρ / 2), DifferentiableAt ℂ f z := by
    intro z hz
    rw [Metric.mem_ball] at hz
    have hzx : ‖z - x‖ < ρ / 2 := by simpa [dist_eq_norm] using hz
    have hzS : z ∈ S := by
      apply hTS
      apply Metric.mem_cthickening_of_dist_le z x ρ T hxT
      rw [dist_eq_norm]
      linarith
    exact hf.differentiableAt (hSo.mem_nhds hzS)
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv (convex_ball x (ρ / 2))
    (Metric.mem_ball_self hρ2pos) (by simpa [dist_eq_norm] using hxy)

end Work.C17g
