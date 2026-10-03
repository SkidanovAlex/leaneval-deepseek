import Mathlib

namespace Work.FatouCH

open Metric Complex

/-- Cauchy estimate for the third derivative of a holomorphic `Φ` whose first derivative is bounded by `C` on `ball z₀ (R-2)`: `‖iteratedDeriv 3 Φ z‖ ≤ 32 C / R²` for `‖z - z₀‖ ≤ 5/4` and `R ≥ 16`. First get `‖iteratedDeriv 2 Φ ζ‖ ≤ 4C/R` on `ball z₀ (R/4)` (Cauchy with radius `R/2 - 2` for `deriv Φ`, via `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`), then Cauchy for `iteratedDeriv 2 Φ` at `z` with radius `R/4 - 2 ≥ R/8`. -/
theorem cauchyIteratedDerivThree {Φ : ℂ → ℂ} {z₀ : ℂ} {R C : ℝ} (hR : 16 ≤ R)
    (hΦ : DifferentiableOn ℂ Φ (Metric.ball z₀ R))
    (hC : ∀ z ∈ Metric.ball z₀ (R - 2), ‖deriv Φ z‖ ≤ C)
    {z : ℂ} (hz : ‖z - z₀‖ ≤ 5 / 4) :
    ‖iteratedDeriv 3 Φ z‖ ≤ 32 * C / R ^ 2 := by
  have hRpos : 0 < R := by linarith
  -- `C` is automatically nonnegative: it dominates `‖deriv Φ z₀‖ ≥ 0`.
  have hCnn : 0 ≤ C := by
    have h0 : z₀ ∈ Metric.ball z₀ (R - 2) := by
      rw [mem_ball, dist_self]; linarith
    have := hC z₀ h0
    linarith [norm_nonneg (deriv Φ z₀)]
  -- `iteratedDeriv 2 Φ = deriv (deriv Φ)` as functions.
  have h2 : iteratedDeriv 2 Φ = deriv (deriv Φ) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hΦ1 : DifferentiableOn ℂ (deriv Φ) (Metric.ball z₀ (R - 2)) :=
    (hΦ.mono (ball_subset_ball (by linarith))).deriv isOpen_ball
  have hΦ2 : DifferentiableOn ℂ (iteratedDeriv 2 Φ) (Metric.ball z₀ (R / 4)) := by
    rw [h2]
    exact (hΦ1.deriv isOpen_ball).mono (ball_subset_ball (by linarith))
  -- Step 1: Cauchy with radius `R/2 - 2` for `deriv Φ` at `ζ ∈ ball z₀ (R/4)`.
  have stepB : ∀ ζ ∈ Metric.ball z₀ (R / 4), ‖iteratedDeriv 2 Φ ζ‖ ≤ 4 * C / R := by
    intro ζ hζ
    have hζd : dist ζ z₀ < R / 4 := by rwa [mem_ball] at hζ
    have hr1 : 0 < R / 2 - 2 := by linarith
    have hsub : closedBall ζ (R / 2 - 2) ⊆ Metric.ball z₀ (R - 2) :=
      closedBall_subset_ball' (by linarith)
    have hd : DiffContOnCl ℂ (deriv Φ) (Metric.ball ζ (R / 2 - 2)) :=
      DifferentiableOn.diffContOnCl_ball hΦ1 hsub
    have hb : ∀ w ∈ Metric.sphere ζ (R / 2 - 2), ‖deriv Φ w‖ ≤ C := fun w hw =>
      hC w (hsub (sphere_subset_closedBall hw))
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr1 hd hb
    rw [← h2] at hc
    refine hc.trans ?_
    rw [div_le_div_iff₀ hr1 hRpos]
    nlinarith
  -- Step 2: Cauchy with radius `R/4 - 2` for `iteratedDeriv 2 Φ` at `z`.
  rw [iteratedDeriv_succ]
  have hzd : dist z z₀ ≤ 5 / 4 := by simpa [dist_eq_norm] using hz
  have hr2 : 0 < R / 4 - 2 := by linarith
  have hsub2 : closedBall z (R / 4 - 2) ⊆ Metric.ball z₀ (R / 4) :=
    closedBall_subset_ball' (by linarith)
  have hd2 : DiffContOnCl ℂ (iteratedDeriv 2 Φ) (Metric.ball z (R / 4 - 2)) :=
    DifferentiableOn.diffContOnCl_ball hΦ2 hsub2
  have hb2 : ∀ w ∈ Metric.sphere z (R / 4 - 2), ‖iteratedDeriv 2 Φ w‖ ≤ 4 * C / R :=
    fun w hw => stepB w (hsub2 (sphere_subset_closedBall hw))
  have hc2 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr2 hd2 hb2
  refine hc2.trans ?_
  rw [div_le_div_iff₀ hr2 (by positivity)]
  have h3 : 4 * C / R * R ^ 2 = 4 * C * R := by field_simp
  rw [h3]
  nlinarith [mul_nonneg hCnn (by linarith : (0 : ℝ) ≤ R - 16)]

end Work.FatouCH
