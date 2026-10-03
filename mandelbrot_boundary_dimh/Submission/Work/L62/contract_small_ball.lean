import Mathlib

/-!
# Contraction on a small ball around an attracting fixed point

If `H` is holomorphic on an open set `Ω ∋ 0`, fixes `0`, and its multiplier
`deriv H 0` has norm `< 1`, then on a sufficiently small ball around `0` still
contained in `Ω` the map `H` is a contraction with some ratio `θ < 1`, and all
its iterates satisfy `‖H^[n] z‖ ≤ θ^n ‖z‖`.

The proof is the elementary one: `H z = H 0 + (fderiv ℂ H 0) z + o(z)` and
`(fderiv ℂ H 0) z = z * deriv H 0`; taking `θ = (1 + ‖deriv H 0‖)/2 < 1` and
using the little-o estimate with `θ - ‖deriv H 0‖ > 0` gives the one-step bound
on a small ball; the iterate bound is an induction, using that the ball is
forward invariant because `H` shrinks norms by `θ ≤ 1`.
-/

namespace Work.L62

open Complex Metric Filter Asymptotics
open scoped Topology

theorem contract_small_ball {Ω : Set ℂ} (hΩo : IsOpen Ω) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H Ω) (h0 : (0 : ℂ) ∈ Ω) (hfix : H 0 = 0)
    (hder : ‖deriv H 0‖ < 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (0 : ℂ) ρ ⊆ Ω ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) ρ, ‖H z‖ ≤ θ * ‖z‖) ∧
      (∀ n : ℕ, ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, ‖(H^[n]) z‖ ≤ θ ^ n * ‖z‖) := by
  -- ## Numerical setup
  set c : ℝ := ‖deriv H 0‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  have hc1 : c < 1 := by rw [hc]; exact hder
  set θ : ℝ := (1 + c) / 2 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hε : 0 < θ - c := by rw [hθ]; linarith
  -- ## `H` is holomorphic at `0`; the differential is multiplication by `deriv H 0`
  have hd : DifferentiableAt ℂ H 0 := hH.differentiableAt (hΩo.mem_nhds h0)
  have hA : ∀ w : ℂ, (fderiv ℂ H 0) w = w * deriv H 0 := by
    intro w
    calc (fderiv ℂ H 0) w = (fderiv ℂ H 0) (w • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
      _ = w • (fderiv ℂ H 0) 1 := map_smul (fderiv ℂ H 0) w 1
      _ = w * deriv H 0 := by rw [smul_eq_mul]; rfl
  -- ## The little-o form of the first order expansion at `0`
  have hlo := hd.hasFDerivAt.isLittleO
  rw [isLittleO_iff] at hlo
  have hev := hlo hε
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr0, hrv⟩ := hev
  obtain ⟨rΩ, hrΩ0, hrΩ⟩ := Metric.mem_nhds_iff.mp (hΩo.mem_nhds h0)
  refine ⟨θ, hθ0, hθ1, ?_⟩
  -- ## Choice of the ball
  set ρ : ℝ := min r rΩ / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρr : ρ < r := by rw [hρ]; have := min_le_left r rΩ; linarith
  have hρΩ : ρ < rΩ := by rw [hρ]; have := min_le_right r rΩ; linarith
  have hsub : Metric.closedBall (0 : ℂ) ρ ⊆ Ω := by
    intro z hz
    apply hrΩ
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  -- ## The one-step contraction on the ball
  have hstep : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, ‖H z‖ ≤ θ * ‖z‖ := by
    intro z hz
    have h1 : ‖z‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hzr : ‖z‖ < r := by linarith
    have hE : ‖H z - H 0 - (fderiv ℂ H 0) (z - 0)‖ ≤ (θ - c) * ‖z‖ := by
      have h2 := hrv (y := z) (by rwa [dist_zero_right])
      simpa using h2
    have hA2 : ‖(fderiv ℂ H 0) (z - 0)‖ = c * ‖z‖ := by
      rw [hA, sub_zero, norm_mul, hc]; ring
    have hsplit :
        H z - H 0 - (fderiv ℂ H 0) (z - 0) + (fderiv ℂ H 0) (z - 0) + H 0 = H z := by ring
    calc ‖H z‖
        = ‖(H z - H 0 - (fderiv ℂ H 0) (z - 0)) + (fderiv ℂ H 0) (z - 0) + H 0‖ := by
          rw [hsplit]
      _ ≤ ‖(H z - H 0 - (fderiv ℂ H 0) (z - 0)) + (fderiv ℂ H 0) (z - 0)‖ + ‖H 0‖ :=
          norm_add_le _ _
      _ = ‖(H z - H 0 - (fderiv ℂ H 0) (z - 0)) + (fderiv ℂ H 0) (z - 0)‖ := by
          rw [hfix, norm_zero, add_zero]
      _ ≤ ‖H z - H 0 - (fderiv ℂ H 0) (z - 0)‖ + ‖(fderiv ℂ H 0) (z - 0)‖ := norm_add_le _ _
      _ ≤ (θ - c) * ‖z‖ + c * ‖z‖ := add_le_add hE (le_of_eq hA2)
      _ = θ * ‖z‖ := by ring
  refine ⟨ρ, hρ0, hsub, hstep, ?_⟩
  -- ## Iterates: induction, the ball being forward invariant since `θ ≤ 1`
  intro n
  induction n with
  | zero => intro z hz; simp
  | succ n ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have hz' : (H^[n]) z ∈ Metric.closedBall (0 : ℂ) ρ := by
      have h2 : ‖z‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖(H^[n]) z‖ ≤ θ ^ n * ‖z‖ := ih z hz
        _ ≤ 1 * ‖z‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (n := n) hθ0 hθ1.le) (norm_nonneg z)
        _ = ‖z‖ := one_mul _
        _ ≤ ρ := h2
    calc ‖H ((H^[n]) z)‖ ≤ θ * ‖(H^[n]) z‖ := hstep _ hz'
      _ ≤ θ * (θ ^ n * ‖z‖) := mul_le_mul_of_nonneg_left (ih z hz) hθ0
      _ = θ ^ n.succ * ‖z‖ := by rw [pow_succ]; ring

end Work.L62
