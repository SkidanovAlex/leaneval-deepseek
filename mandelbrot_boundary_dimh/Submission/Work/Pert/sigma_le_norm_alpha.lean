import Mathlib

namespace Work.Pert

/-- Perturbation bound (Shishikura, Appendix A.1): if `1 - σ·u₀ = exp (2πi α)` with
`‖α‖ ≤ 1/64` and `‖u₀‖ ≥ 1/2`, then `‖σ‖ ≤ 32 ‖α‖`.

Indeed `σ u₀ = 1 - exp w` with `w = 2πi α`, `‖w‖ = 2π‖α‖ ≤ π/32 ≤ 1`, so the quadratic
Taylor bound `Complex.norm_exp_sub_one_le` gives `‖exp w - 1‖ ≤ 2‖w‖ = 4π‖α‖`.  Hence
`‖σ‖‖u₀‖ = ‖exp w - 1‖ ≤ 4π‖α‖`, and `‖u₀‖ ≥ 1/2` yields `‖σ‖ ≤ 8π‖α‖ ≤ 32‖α‖`
(using `π < 4`). -/
theorem sigma_le_norm_alpha {α σ u₀ : ℂ} (hα : ‖α‖ ≤ 1 / 64) (hu₀ : 1 / 2 ≤ ‖u₀‖)
    (hnorm : 1 - σ * u₀ = Complex.exp (2 * Real.pi * Complex.I * α)) :
    ‖σ‖ ≤ 32 * ‖α‖ := by
  set w : ℂ := 2 * Real.pi * Complex.I * α with hw
  have hwn : ‖w‖ = 2 * Real.pi * ‖α‖ := by
    rw [hw, norm_mul, norm_mul, norm_mul]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
        show ‖(Real.pi : ℂ)‖ = Real.pi by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos],
        Complex.norm_I, mul_one]
  have hwle : ‖w‖ ≤ 1 := by
    rw [hwn]
    nlinarith [hα, Real.pi_lt_four, norm_nonneg α]
  have hσu : σ * u₀ = 1 - Complex.exp w := by
    rw [← hnorm]; ring
  have hprod : ‖σ‖ * ‖u₀‖ = ‖Complex.exp w - 1‖ := by
    rw [← norm_mul, hσu, norm_sub_rev]
  have hexp : ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := Complex.norm_exp_sub_one_le hwle
  have hmain : ‖σ‖ * ‖u₀‖ ≤ 4 * Real.pi * ‖α‖ := by
    calc ‖σ‖ * ‖u₀‖ = ‖Complex.exp w - 1‖ := hprod
      _ ≤ 2 * ‖w‖ := hexp
      _ = 4 * Real.pi * ‖α‖ := by rw [hwn]; ring
  have h2 : ‖σ‖ * (1 / 2) ≤ 4 * Real.pi * ‖α‖ :=
    le_trans (mul_le_mul_of_nonneg_left hu₀ (norm_nonneg σ)) hmain
  have h1 : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := by linarith
  have h3 : 8 * Real.pi * ‖α‖ ≤ 32 * ‖α‖ := by
    nlinarith [Real.pi_lt_four, norm_nonneg α]
  linarith

end Work.Pert
