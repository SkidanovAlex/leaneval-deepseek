import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Pin3.exp_near_lower

/-!
# PERT · `Work.Pert.Pin3.Prelim`

Elementary quantitative bounds for the perturbed perturbation data of Shishikura §4.2:

* `norm_sigma_le14` — `‖σ‖ ≤ 14‖α‖` from the normalisation `1 - σ u 0 = exp (2πiα)`;
* `tauC_le_inv` — `‖τ_f z‖ ≤ 9/‖z‖` when `‖2πiαz‖ ≤ 2/5` and `‖σ‖ ≤ 14‖α‖`.

These are shared by the files of the `Pin3` area, so they live in their own module.
-/

namespace Work.Pert.Pin3

open Complex

noncomputable section

/-- `‖σ‖ ≤ 14 ‖α‖` from the normalisation `1 - σ u 0 = exp (2πiα)`. -/
lemma norm_sigma_le14 {u : ℂ → ℂ} {σ α : ℂ} {r : ℝ} (_hr : 0 < r)
    (hu0 : 1 / 2 ≤ ‖u 0‖)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hα : ‖α‖ ≤ 1 / 64) :
    ‖σ‖ ≤ 14 * ‖α‖ := by
  set w : ℂ := 2 * Real.pi * Complex.I * α with hw
  have hwn : ‖w‖ = 2 * Real.pi * ‖α‖ := by
    rw [hw, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_I]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
        show ‖(Real.pi : ℂ)‖ = Real.pi by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]]
    ring
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hwn]; nlinarith [Real.pi_le_four, norm_nonneg α, hα]
  have hexp : ‖Complex.exp w - 1‖ ≤ ‖w‖ * (1 + ‖w‖) := by
    have hrem := Complex.norm_exp_sub_one_sub_id_le hw1
    have he : Complex.exp w - 1 = (Complex.exp w - 1 - w) + w := by ring
    rw [he]
    calc ‖(Complex.exp w - 1 - w) + w‖ ≤ ‖Complex.exp w - 1 - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖ ^ 2 + ‖w‖ := by linarith
      _ = ‖w‖ * (1 + ‖w‖) := by ring
  have hσu : ‖σ * u 0‖ = ‖Complex.exp w - 1‖ := by
    have h : σ * u 0 = 1 - Complex.exp w := by
      have h2 := hnorm
      rw [hw] at h2
      linear_combination (-1 : ℂ) * h2
    rw [h, norm_sub_rev]
  have hw10 : ‖w‖ ≤ 1 / 10 := by
    rw [hwn]; nlinarith [Real.pi_lt_d2, norm_nonneg α, hα]
  have hstep : ‖σ‖ * (1 / 2) ≤ (2 * Real.pi * ‖α‖) * (1 + 1 / 10) := by
    calc ‖σ‖ * (1 / 2) ≤ ‖σ‖ * ‖u 0‖ := mul_le_mul_of_nonneg_left hu0 (norm_nonneg σ)
      _ = ‖σ * u 0‖ := (norm_mul _ _).symm
      _ = ‖Complex.exp w - 1‖ := hσu
      _ ≤ ‖w‖ * (1 + ‖w‖) := hexp
      _ ≤ (2 * Real.pi * ‖α‖) * (1 + 1 / 10) := by
          apply mul_le_mul
          · rw [hwn]
          · linarith
          · positivity
          · positivity
  have hnum : (2 * Real.pi * ‖α‖) * (1 + 1 / 10) ≤ 7 * ‖α‖ := by
    nlinarith [Real.pi_lt_d2, norm_nonneg α]
  linarith [hstep, hnum]

/-- `‖τ_f z‖ ≤ 9 / ‖z‖` when `‖2πiαz‖ ≤ 2/5` and `‖σ‖ ≤ 14‖α‖`. -/
lemma tauC_le_inv {σ α z : ℂ} (hαne : α ≠ 0) (hσ : ‖σ‖ ≤ 14 * ‖α‖)
    (hw : ‖2 * Real.pi * Complex.I * α * z‖ ≤ 2 / 5) (hz : 0 < ‖z‖) :
    ‖Work.Pert.tauC σ α z‖ ≤ 9 / ‖z‖ := by
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hwn : ‖2 * Real.pi * Complex.I * α * z‖ = 2 * Real.pi * ‖α‖ * ‖z‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_I]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
        show ‖(Real.pi : ℂ)‖ = Real.pi by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]]
    ring
  have hElow : 2 * Real.pi * ‖α‖ * ‖z‖ / 2 ≤
      ‖(1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * z))‖ := by
    have h := exp_near_lower (w := -(2 * Real.pi * Complex.I * α * z)) (by
      rw [hwn] at hw
      rw [norm_neg, hwn]
      exact hw)
    rwa [norm_neg, hwn] at h
  have hpos : 0 < 2 * Real.pi * ‖α‖ * ‖z‖ / 2 := by positivity
  have hden : 0 < ‖(1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * z))‖ :=
    lt_of_lt_of_le hpos hElow
  rw [Work.Pert.tauC, norm_div]
  refine le_trans (div_le_div₀ (by positivity) hσ hpos hElow) ?_
  have hsimp : (14 * ‖α‖) / (2 * Real.pi * ‖α‖ * ‖z‖ / 2) = 14 / (Real.pi * ‖z‖) := by
    field_simp
  rw [hsimp]
  rw [div_le_div_iff₀ (by positivity) hz]
  nlinarith [Real.pi_gt_three]

end

end Work.Pert.Pin3
