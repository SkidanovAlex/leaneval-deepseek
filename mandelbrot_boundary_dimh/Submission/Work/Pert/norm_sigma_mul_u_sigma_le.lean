import Mathlib

/-!
# PERT · `‖σ · u σ‖ ≤ π/4`

`Work.Pert.norm_sigma_mul_u_sigma_le` (Shishikura, Appendix A.1).

Hypotheses: `1 - σ·u 0 = exp (2πi α)` with `‖α‖ ≤ 1/64`, `‖σ‖ < rr`, and `u` bounded
above and below by `2` and `1/2` on `ball 0 rr`.

Then `σ u₀ = 1 - exp (2πi α)`, so

  `‖σ‖ ‖u 0‖ = ‖1 - exp (2πi α)‖ = ‖exp z - 1‖ ≤ 2‖z‖ = 4π‖α‖ ≤ π/16`,

where `z = 2πi α`, `‖z‖ = 2π‖α‖ ≤ π/32 ≤ 1` and `Complex.norm_exp_sub_one_le` applies.
Since `‖u 0‖ ≥ 1/2` this gives `‖σ‖ ≤ π/8`, and since `σ ∈ ball 0 rr` (as `‖σ‖ < rr`)
we have `‖u σ‖ ≤ 2`, whence `‖σ u σ‖ ≤ (π/8)·2 = π/4`.
-/

namespace Work.Pert

theorem norm_sigma_mul_u_sigma_le {rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hrr : 0 < rr) (hσr : ‖σ‖ < rr) (hα64 : ‖α‖ ≤ 1 / 64)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) :
    ‖σ * u σ‖ ≤ Real.pi / 4 := by
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hrr
  have hσmem : σ ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_zero_right]; exact hσr
  obtain ⟨hu0ge, -⟩ := hu2 0 h0mem
  obtain ⟨-, huσle⟩ := hu2 σ hσmem
  set z : ℂ := 2 * Real.pi * Complex.I * α with hz
  have hnorm' : 1 - σ * u 0 = Complex.exp z := hnorm.trans (congrArg Complex.exp hz.symm)
  have hzn : ‖z‖ = 2 * Real.pi * ‖α‖ := by
    rw [hz, norm_mul, norm_mul, norm_mul]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
        show ‖(Real.pi : ℂ)‖ = Real.pi by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos],
        Complex.norm_I]
    ring
  have hzle1 : ‖z‖ ≤ 1 := by
    rw [hzn]
    nlinarith [hα64, norm_nonneg α, Real.pi_lt_four]
  have hexp : ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := Complex.norm_exp_sub_one_le hzle1
  have hσu : σ * u 0 = 1 - Complex.exp z := by rw [← hnorm']; ring
  have hprod : ‖σ‖ * ‖u 0‖ = ‖Complex.exp z - 1‖ := by
    rw [← norm_mul, hσu, norm_sub_rev]
  have hu0pos : 0 < ‖u 0‖ := by linarith
  have h1 : ‖σ‖ * ‖u 0‖ ≤ Real.pi / 16 := by
    rw [hprod]
    calc ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := hexp
      _ = 4 * Real.pi * ‖α‖ := by rw [hzn]; ring
      _ ≤ 4 * Real.pi * (1 / 64) := by
          exact mul_le_mul_of_nonneg_left hα64 (by positivity)
      _ = Real.pi / 16 := by ring
  have hinv : 1 / ‖u 0‖ ≤ 2 := by
    rw [div_le_iff₀ hu0pos]; linarith
  have hσle : ‖σ‖ ≤ Real.pi / 8 := by
    calc ‖σ‖ = ‖σ‖ * ‖u 0‖ / ‖u 0‖ := (mul_div_cancel_right₀ ‖σ‖ (ne_of_gt hu0pos)).symm
      _ ≤ (Real.pi / 16) / ‖u 0‖ := div_le_div_of_nonneg_right h1 hu0pos.le
      _ = Real.pi / 16 * (1 / ‖u 0‖) := by rw [div_eq_mul_one_div]
      _ ≤ Real.pi / 16 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = Real.pi / 8 := by ring
  calc ‖σ * u σ‖ = ‖σ‖ * ‖u σ‖ := norm_mul σ (u σ)
    _ ≤ Real.pi / 8 * 2 := mul_le_mul hσle huσle (norm_nonneg _) (by positivity)
    _ = Real.pi / 4 := by ring

end Work.Pert
