import Mathlib

namespace Work.Pert.LiftExp

/-- If `1 - σ·u 0 = exp (2πi α)` with `‖α‖ ≤ 1/64` and `‖u 0‖ ≥ 1/2`, then `‖σ‖ ≤ 1`.

Indeed `σ u 0 = 1 - exp z` with `z = 2πi α`, `‖z‖ = 2π‖α‖ ≤ π/32 ≤ 1`, so the quadratic
Taylor estimate `‖exp z - 1‖ ≤ 2‖z‖` (valid on the unit disc) gives
`‖σ‖ ‖u 0‖ ≤ 4π‖α‖ ≤ π/16`, hence `‖σ‖ ≤ 2·π/16 = π/8 < 1`. -/
theorem norm_sigma_add_one_le_two {u : ℂ → ℂ} {σ α : ℂ}
    (hαsmall : ‖α‖ ≤ 1 / 64)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu0 : 1 / 2 ≤ ‖u 0‖) : ‖σ‖ + 1 ≤ 2 := by
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
    nlinarith [hαsmall, norm_nonneg α, Real.pi_lt_four]
  have hexp : ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := Complex.norm_exp_sub_one_le hzle1
  have hσu : σ * u 0 = 1 - Complex.exp z := by rw [← hnorm']; ring
  have hprod : ‖σ‖ * ‖u 0‖ = ‖Complex.exp z - 1‖ := by
    rw [← norm_mul, hσu, norm_sub_rev]
  have hu0pos : 0 < ‖u 0‖ := by linarith
  have h1 : ‖σ‖ * ‖u 0‖ ≤ Real.pi / 16 := by
    rw [hprod]
    calc ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := hexp
      _ = 4 * Real.pi * ‖α‖ := by rw [hzn]; ring
      _ ≤ 4 * Real.pi * (1 / 64) :=
          mul_le_mul_of_nonneg_left hαsmall (by positivity)
      _ = Real.pi / 16 := by ring
  have hinv : 1 / ‖u 0‖ ≤ 2 := by
    rw [div_le_iff₀ hu0pos]; linarith
  have hσ : ‖σ‖ ≤ Real.pi / 8 := by
    calc ‖σ‖ = ‖σ‖ * ‖u 0‖ / ‖u 0‖ := (mul_div_cancel_right₀ ‖σ‖ (ne_of_gt hu0pos)).symm
      _ ≤ (Real.pi / 16) / ‖u 0‖ := div_le_div_of_nonneg_right h1 hu0pos.le
      _ = Real.pi / 16 * (1 / ‖u 0‖) := by rw [div_eq_mul_one_div]
      _ ≤ Real.pi / 16 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = Real.pi / 8 := by ring
  have hpi : Real.pi / 8 ≤ 1 := by linarith [Real.pi_lt_four]
  linarith

end Work.Pert.LiftExp
