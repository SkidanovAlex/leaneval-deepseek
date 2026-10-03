import Mathlib

/-!
# `Work.Analysis.ZetaLocal.zeta_sigma_prelim`

Numerical handles on the second fixed point `σ` of `f z = z + z (z - σ) u z`, obtained from the
normalisation `1 - σ u 0 = exp (2πiα)`, the two-sided bound `1/2 ≤ ‖u‖ ≤ 2` near `0` and the
Lipschitz hypothesis on `u`; the only smallness input is `hsmall : (2π + 32C)‖α‖ ≤ 1/128`.

Write `T = 1 - exp (2πiα) = σ u 0`.

* `‖T‖ ≤ 4π‖α‖ ≤ 1/64`, by `Complex.norm_exp_sub_one_le` (`‖1 - exp w‖ ≤ 2‖w‖` for `‖w‖ ≤ 1`).
* Hence `‖σ‖ ≤ 2‖T‖ ≤ 8π‖α‖ ≤ 1/32`, and `C‖σ‖ ≤ 8π C‖α‖ ≤ π/512 ≤ 1`.
* Since `1 + σ u σ = (2 - exp (2πiα)) + σ (u σ - u 0)` and
  `‖σ (u σ - u 0)‖ ≤ ‖σ‖ C‖σ‖ ≤ 1/32`, the real part is `≥ 63/64 - 1/32 = 61/64`, whence the
  norm bound; the imaginary part is `-Im T + Im (σ (u σ - u 0))`, bounded by `1/64 + 1/32`.
* The last conjunct is the Lipschitz estimate at `σ, 0 ∈ ball 0 r`.

Note (name resolution only, statement unchanged): the imaginary unit is written as the bare `I`,
which is `Complex.I`; `open Complex` below is what makes it resolve under `autoImplicit = false`
(as used by `lake build`).
-/

set_option autoImplicit false

open Complex

namespace Work.Analysis.ZetaLocal

theorem zeta_sigma_prelim {u : ℂ → ℂ} {σ α : ℂ} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hu2 : ∀ z ∈ Metric.ball 0 r, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (huL : ∀ z ∈ Metric.ball 0 r, ∀ w ∈ Metric.ball 0 r, ‖u z - u w‖ ≤ C * ‖z - w‖)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * I * α))
    (hσr : ‖σ‖ < r) (hαne : α ≠ 0)
    (hsmall : (2 * Real.pi + 32 * C) * ‖α‖ ≤ 1 / 128) :
    ‖σ‖ ≤ 1 / 32 ∧ C * ‖σ‖ ≤ 1 ∧ 1 / 2 ≤ (1 + σ * u σ).re ∧
    1 / 2 ≤ ‖1 + σ * u σ‖ ∧ |(1 + σ * u σ).im| ≤ 1 / 64 + 1 / 32 ∧
    ‖u σ - u 0‖ ≤ C * ‖σ‖ := by
  have _hα : α ≠ 0 := hαne
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  have hσmem : σ ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hσr
  have hu0 : 1 / 2 ≤ ‖u 0‖ ∧ ‖u 0‖ ≤ 2 := hu2 0 h0mem
  have h2p : 2 * Real.pi * ‖α‖ ≤ 1 / 128 := by
    have h1 : 2 * Real.pi * ‖α‖ ≤ (2 * Real.pi + 32 * C) * ‖α‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg α)
    linarith
  have h32 : 32 * C * ‖α‖ ≤ 1 / 128 := by
    have h1 : 32 * C * ‖α‖ ≤ (2 * Real.pi + 32 * C) * ‖α‖ :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_pos]) (norm_nonneg α)
    linarith
  have hCα : C * ‖α‖ ≤ 1 / 4096 := by linarith
  have hwnorm : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have hw1 : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ ≤ 1 := by rw [hwnorm]; linarith
  have hA1 : ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ ≤ 4 * Real.pi * ‖α‖ := by
    have h := Complex.norm_exp_sub_one_le hw1
    rw [hwnorm] at h
    linarith
  have hA1' : ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ ≤ 1 / 64 := by linarith
  have hσu0 : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    linear_combination (-1 : ℂ) * hnorm
  have hσ_norm : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := by
    have h1 : ‖σ‖ * ‖u 0‖ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
      rw [← norm_mul, hσu0]
    have h2 : ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖
        = ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ := norm_sub_rev _ _
    have h3 : ‖σ‖ * (1 / 2) ≤ ‖σ‖ * ‖u 0‖ :=
      mul_le_mul_of_nonneg_left hu0.1 (norm_nonneg σ)
    nlinarith [h1, h2, hA1, h3, norm_nonneg σ]
  have hσ32 : ‖σ‖ ≤ 1 / 32 := by nlinarith [hσ_norm, h2p, Real.pi_pos]
  have hCσ : C * ‖σ‖ ≤ 1 := by
    have h1 : C * ‖σ‖ ≤ C * (8 * Real.pi * ‖α‖) := mul_le_mul_of_nonneg_left hσ_norm hC
    nlinarith [h1, hCα, Real.pi_lt_four, Real.pi_pos]
  have hlipσ : ‖u σ - u 0‖ ≤ C * ‖σ‖ := by
    have h := huL σ hσmem 0 h0mem
    simpa using h
  have hW : ‖σ * (u σ - u 0)‖ ≤ 1 / 32 := by
    rw [norm_mul]
    have h1 : ‖σ‖ * ‖u σ - u 0‖ ≤ ‖σ‖ * (C * ‖σ‖) :=
      mul_le_mul_of_nonneg_left hlipσ (norm_nonneg σ)
    nlinarith [h1, hCσ, hσ32, norm_nonneg σ]
  have hD : 1 + σ * u σ = (2 - Complex.exp (2 * Real.pi * Complex.I * α)) + σ * (u σ - u 0) := by
    have h1 : σ * u σ = σ * u 0 + σ * (u σ - u 0) := by ring
    rw [h1, hσu0]; ring
  have habs : |(Complex.exp (2 * Real.pi * Complex.I * α)).re - 1| ≤ 1 / 64 := by
    have h := Complex.abs_re_le_norm (Complex.exp (2 * Real.pi * Complex.I * α) - 1)
    have h2 : (Complex.exp (2 * Real.pi * Complex.I * α) - 1).re
        = (Complex.exp (2 * Real.pi * Complex.I * α)).re - 1 := by simp
    rw [h2] at h
    linarith
  have hAre_le : (Complex.exp (2 * Real.pi * Complex.I * α)).re ≤ 1 + 1 / 64 := by
    have := (abs_le.mp habs).2; linarith
  have h2A : 63 / 64 ≤ ‖(2 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
    have h1 : ‖(2 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * α)‖
        = ‖(1 : ℂ) - (Complex.exp (2 * Real.pi * Complex.I * α) - 1)‖ := by
      congr 1; ring
    rw [h1]
    have h := abs_norm_sub_norm_le (1 : ℂ) (Complex.exp (2 * Real.pi * Complex.I * α) - 1)
    rw [norm_one] at h
    have h4 : |(1:ℝ) - ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖|
        ≤ ‖(1 : ℂ) - (Complex.exp (2 * Real.pi * Complex.I * α) - 1)‖ := h
    have h3 : (1 : ℝ) - ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖
        ≤ |1 - ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖| := le_abs_self _
    linarith
  have h2re : ((2 : ℂ)).re = 2 := by norm_num
  have h2im : ((2 : ℂ)).im = 0 := by norm_num
  have hDre : 1 / 2 ≤ (1 + σ * u σ).re := by
    rw [hD]
    simp only [Complex.add_re, Complex.sub_re]
    rw [h2re]
    have h := Complex.abs_re_le_norm (σ * (u σ - u 0))
    rw [abs_le] at h
    linarith [h.1, hW, hAre_le]
  have hDnorm : 1 / 2 ≤ ‖1 + σ * u σ‖ := by
    rw [hD]
    have h := norm_add_le ((2 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * α)
      + σ * (u σ - u 0)) (-(σ * (u σ - u 0)))
    rw [add_neg_cancel_right, norm_neg] at h
    linarith [h, h2A, hW]
  have hDim : |(1 + σ * u σ).im| ≤ 1 / 64 + 1 / 32 := by
    rw [hD]
    simp only [Complex.add_im, Complex.sub_im]
    rw [h2im, zero_sub]
    have h1 : |(Complex.exp (2 * Real.pi * Complex.I * α)).im| ≤ 1 / 64 := by
      have h := Complex.abs_im_le_norm (Complex.exp (2 * Real.pi * Complex.I * α) - 1)
      have h2 : (Complex.exp (2 * Real.pi * Complex.I * α) - 1).im
          = (Complex.exp (2 * Real.pi * Complex.I * α)).im := by simp
      rw [h2] at h
      linarith
    have h2 : |(σ * (u σ - u 0)).im| ≤ 1 / 32 :=
      le_trans (Complex.abs_im_le_norm _) hW
    have h3 : |-(Complex.exp (2 * Real.pi * Complex.I * α)).im + (σ * (u σ - u 0)).im|
        ≤ |(Complex.exp (2 * Real.pi * Complex.I * α)).im| + |(σ * (u σ - u 0)).im| := by
      have h := abs_add_le (-(Complex.exp (2 * Real.pi * Complex.I * α)).im)
        ((σ * (u σ - u 0)).im)
      rwa [abs_neg] at h
    linarith
  exact ⟨hσ32, hCσ, hDre, hDnorm, hDim, hlipσ⟩


end Work.Analysis.ZetaLocal
