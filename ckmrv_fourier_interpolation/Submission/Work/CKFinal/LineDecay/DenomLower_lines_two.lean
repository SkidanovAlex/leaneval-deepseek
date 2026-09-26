import Mathlib
import Submission.Work.CKFinal.LineDecay.DenomLower_lines

noncomputable section
open UpperHalfPlane
set_option maxHeartbeats 1000000

namespace Work.CKFinal.LineDecay

/-! ## Denominator lower bound on the two lines, `Im τ ≥ 2`

This is the `Y₀ = 2` specialisation of `Work.CKFinal.LineDecay.DenomLower_lines`
(the two-leading-terms-add estimate on the lines `Re τ = ±1/2`).  The only change is
that the height hypothesis `Y₀ ≤ Im τ` is replaced by the explicit `2 ≤ Im τ`, which is
exactly the constant used in the proof of `DenomLower_lines`. -/
theorem DenomLower_lines_two :
    ∃ c : ℝ, 0 < c ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → 2 ≤ τ.im → 1 ≤ t →
        c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
          ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
              (Work.Kernels.jInvariantFun τ
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro τ t ht hline him ht1
  set zz : UpperHalfPlane := Work.Kernels.imagAxis t ht with hzzdef
  have hzz_im : zz.im = t := by
    rw [hzzdef]; simp [Work.Kernels.imagAxis, UpperHalfPlane.im]
  have hzz1 : (1 : ℝ) ≤ zz.im := by rw [hzz_im]; exact ht1
  have him1 : (1 : ℝ) ≤ τ.im := by linarith
  set a : ℝ := Real.exp (-(2 * Real.pi * t)) with hadef
  set b : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with hbdef
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have ha512 : a ≤ 1 / 512 := by
    rw [hadef]
    have h1 : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(2 * Real.pi)) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, ht1]
    linarith [Work.Asymptotics.exp_neg_two_pi_le_inv512]
  have hb25 : b ≤ 1 / 262144 := by
    rw [hbdef]
    have h1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(4 * Real.pi)) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, him]
    have h2 : Real.exp (-(4 * Real.pi)) ≤ (1 : ℝ) / 262144 := by
      have h3 : Real.exp (-(4 * Real.pi)) = Real.exp (-(2 * Real.pi)) ^ 2 := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      rw [h3]
      have h4 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi)) := (Real.exp_pos _).le
      nlinarith [Work.Asymptotics.exp_neg_two_pi_le_inv512, h4]
    linarith
  have hqz : Work.Kernels.qParamFun zz = (a : ℂ) := by
    rw [hzzdef, qParamFun_imagAxis t ht, hadef]
  have hqτ : Work.Kernels.qParamFun τ = -(b : ℂ) := by
    rw [qParamFun_line_half τ hline, hbdef]
  have hnqz : ‖Work.Kernels.qParamFun zz‖ = a := by
    rw [Work.Asymptotics.norm_qParamFun, hzz_im, hadef]
  have hnqτ : ‖Work.Kernels.qParamFun τ‖ = b := by
    rw [Work.Asymptotics.norm_qParamFun, hbdef]
  have hΔz : ‖Work.Kernels.DeltaFun zz - (a : ℂ)‖ ≤ (1 / 20) * a := by
    have h := Delta_first_order_lin zz hzz1
    rw [hnqz, hqz] at h
    exact h
  have hΔτ : ‖Work.Kernels.DeltaFun τ + (b : ℂ)‖ ≤ (1 / 20) * b := by
    have h := Delta_first_order_lin τ him1
    rw [hnqτ, hqτ] at h
    simpa using h
  have hΔz_re : a - (1 / 20) * a ≤ (Work.Kernels.DeltaFun zz).re := by
    have h1 : -(‖Work.Kernels.DeltaFun zz - (a : ℂ)‖)
        ≤ (Work.Kernels.DeltaFun zz - (a : ℂ)).re := neg_norm_le_re _
    have h2 : (Work.Kernels.DeltaFun zz).re
        = a + (Work.Kernels.DeltaFun zz - (a : ℂ)).re := by
      rw [Complex.sub_re, Complex.ofReal_re]; ring
    rw [h2]; linarith
  have hΔz_im : |(Work.Kernels.DeltaFun zz).im| ≤ (1 / 20) * a := by
    have h2 : (Work.Kernels.DeltaFun zz).im = (Work.Kernels.DeltaFun zz - (a : ℂ)).im := by
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [h2]
    exact le_trans (Complex.abs_im_le_norm _) hΔz
  have hΔτ_re : b - (1 / 20) * b ≤ (-(Work.Kernels.DeltaFun τ)).re := by
    have h1 : (Work.Kernels.DeltaFun τ + (b : ℂ)).re
        ≤ ‖Work.Kernels.DeltaFun τ + (b : ℂ)‖ := Complex.re_le_norm _
    have h2 : (-(Work.Kernels.DeltaFun τ)).re
        = b - (Work.Kernels.DeltaFun τ + (b : ℂ)).re := by
      rw [Complex.neg_re, Complex.add_re, Complex.ofReal_re]; ring
    rw [h2]; linarith
  have hΔτ_im : |(-(Work.Kernels.DeltaFun τ)).im| ≤ (1 / 20) * b := by
    have h2 : (-(Work.Kernels.DeltaFun τ)).im
        = -((Work.Kernels.DeltaFun τ + (b : ℂ)).im) := by
      rw [Complex.neg_im, Complex.add_im, Complex.ofReal_im, add_zero]
    rw [h2, abs_neg]
    exact le_trans (Complex.abs_im_le_norm _) hΔτ
  -- E₄ at z
  set ξz : ℂ := Work.Kernels.E4Fun zz - 1 - 240 * Work.Kernels.qParamFun zz with hξzdef
  have hξz : ‖ξz‖ ≤ 40000 * a ^ 2 := by
    rw [hξzdef]
    have h := E4_two_term_explicit zz hzz1
    rw [hnqz, hqz] at h
    simpa [hqz] using h
  have hξz80 : ‖ξz‖ ≤ 80 * a := by
    refine le_trans hξz ?_
    nlinarith [ha0, ha512]
  have hE4z : Work.Kernels.E4Fun zz = 1 + 240 * (a : ℂ) + ξz := by
    rw [hξzdef, hqz]; ring
  have hE4z_re : (Work.Kernels.E4Fun zz).re = 1 + 240 * a + ξz.re := by
    rw [hE4z]; simp [Complex.add_re, Complex.mul_re]
  have hE4z_im : (Work.Kernels.E4Fun zz).im = ξz.im := by
    rw [hE4z]; simp
  have hwz_re_lo : 1 + 160 * a ≤ (Work.Kernels.E4Fun zz).re := by
    rw [hE4z_re]
    have h : -‖ξz‖ ≤ ξz.re := neg_norm_le_re ξz
    linarith
  have hwz_re_hi : (Work.Kernels.E4Fun zz).re ≤ 1 + 320 * a := by
    rw [hE4z_re]
    have h : ξz.re ≤ ‖ξz‖ := Complex.re_le_norm ξz
    linarith
  have hwz_im : |(Work.Kernels.E4Fun zz).im| ≤ 80 * a := by
    rw [hE4z_im]
    exact le_trans (Complex.abs_im_le_norm ξz) hξz80
  have hwz_norm : ‖Work.Kernels.E4Fun zz‖ ≤ 1 + 320 * a := by
    rw [hE4z]
    have h1 : ‖(1 : ℂ) + 240 * (a : ℂ)‖ ≤ 1 + 240 * a := by
      have h2 : ‖(240 : ℂ) * (a : ℂ)‖ = 240 * a := by
        rw [show (240 : ℂ) * (a : ℂ) = ((240 * a : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc ‖(1 : ℂ) + 240 * (a : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(240 : ℂ) * (a : ℂ)‖ := norm_add_le _ _
        _ = 1 + 240 * a := by rw [h2]; norm_num
    calc ‖1 + 240 * (a : ℂ) + ξz‖ ≤ ‖1 + 240 * (a : ℂ)‖ + ‖ξz‖ := norm_add_le _ _
      _ ≤ (1 + 240 * a) + 80 * a := by linarith
      _ = 1 + 320 * a := by ring
  have hWz_re : 1 ≤ (Work.Kernels.E4Fun zz ^ 3).re := by
    have h := re_cube_lower (w := Work.Kernels.E4Fun zz) hwz_re_lo hwz_re_hi hwz_im
      (by linarith) (by positivity)
    have hnum : (1 : ℝ) ≤ (1 + 160 * a) ^ 3 - 3 * (1 + 320 * a) * (80 * a) ^ 2 := by
      nlinarith [ha0, ha512]
    linarith
  have hWz_norm : ‖Work.Kernels.E4Fun zz ^ 3‖ ≤ 5 := by
    rw [norm_pow]
    calc ‖Work.Kernels.E4Fun zz‖ ^ 3 ≤ (1 + 320 * a) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) hwz_norm 3
      _ ≤ 5 := by nlinarith [ha0, ha512]
  -- E₄ at τ
  set ξτ : ℂ := Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ with hξτdef
  have hξτ : ‖ξτ‖ ≤ 40000 * b ^ 2 := by
    rw [hξτdef]
    have h := E4_two_term_explicit τ him1
    rw [hnqτ, hqτ] at h
    simpa [hqτ] using h
  have hb_small : 40000 * b ^ 2 ≤ 240 * b := by nlinarith [hb0, hb25]
  have hE4τ : Work.Kernels.E4Fun τ = 1 - 240 * (b : ℂ) + ξτ := by
    rw [hξτdef, hqτ]; ring
  have hE4τ_re : (Work.Kernels.E4Fun τ).re = 1 - 240 * b + ξτ.re := by
    rw [hE4τ]; simp [Complex.add_re, Complex.mul_re]
  have hE4τ_im : (Work.Kernels.E4Fun τ).im = ξτ.im := by
    rw [hE4τ]; simp
  have hwτ_re_lo : 1 - 240 * b - 40000 * b ^ 2 ≤ (Work.Kernels.E4Fun τ).re := by
    rw [hE4τ_re]
    have h : -‖ξτ‖ ≤ ξτ.re := neg_norm_le_re ξτ
    linarith
  have hwτ_re_hi : (Work.Kernels.E4Fun τ).re ≤ 1 := by
    rw [hE4τ_re]
    have h : ξτ.re ≤ ‖ξτ‖ := Complex.re_le_norm ξτ
    linarith
  have hwτ_im : |(Work.Kernels.E4Fun τ).im| ≤ 40000 * b ^ 2 := by
    rw [hE4τ_im]
    exact le_trans (Complex.abs_im_le_norm ξτ) hξτ
  have hwτ_norm : ‖Work.Kernels.E4Fun τ‖ ≤ 1 := by
    rw [hE4τ]
    have h1 : ‖(1 : ℂ) - 240 * (b : ℂ)‖ = 1 - 240 * b := by
      rw [show (1 : ℂ) - 240 * (b : ℂ) = ((1 - 240 * b : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    calc ‖1 - 240 * (b : ℂ) + ξτ‖ ≤ ‖1 - 240 * (b : ℂ)‖ + ‖ξτ‖ := norm_add_le _ _
      _ = (1 - 240 * b) + ‖ξτ‖ := by rw [h1]
      _ ≤ 1 := by linarith
  have hWτ_re : (99 : ℝ) / 100 ≤ (Work.Kernels.E4Fun τ ^ 3).re := by
    have h := re_cube_lower (w := Work.Kernels.E4Fun τ) hwτ_re_lo hwτ_re_hi hwτ_im
      (by linarith) (by positivity)
    have hnum : (99 : ℝ) / 100
        ≤ (1 - 240 * b - 40000 * b ^ 2) ^ 3 - 3 * 1 * (40000 * b ^ 2) ^ 2 := by
      nlinarith [hb0, hb25]
    linarith
  have hWτ_norm : ‖Work.Kernels.E4Fun τ ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    calc ‖Work.Kernels.E4Fun τ‖ ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hwτ_norm 3
      _ = 1 := by norm_num
  -- assembly
  have hmain : (1 / 2) * (a + b)
      ≤ (Work.Kernels.DeltaFun zz * Work.Kernels.E4Fun τ ^ 3
          - Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun zz ^ 3).re := by
    have hA := re_mul_lower (u := Work.Kernels.DeltaFun zz) (w := Work.Kernels.E4Fun τ ^ 3)
      (r := a - (1 / 20) * a) (t := (1 / 20) * a) hΔz_re hΔz_im
      (by linarith [hWτ_re]) (by linarith)
    have hB := re_mul_lower (u := -(Work.Kernels.DeltaFun τ)) (w := Work.Kernels.E4Fun zz ^ 3)
      (r := b - (1 / 20) * b) (t := (1 / 20) * b) hΔτ_re hΔτ_im
      (by linarith [hWz_re]) (by linarith)
    have hsplit : (Work.Kernels.DeltaFun zz * Work.Kernels.E4Fun τ ^ 3
          - Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun zz ^ 3).re
        = (Work.Kernels.DeltaFun zz * Work.Kernels.E4Fun τ ^ 3).re
          + (-(Work.Kernels.DeltaFun τ) * Work.Kernels.E4Fun zz ^ 3).re := by
      rw [Complex.sub_re, neg_mul, Complex.neg_re]
      ring
    rw [hsplit]
    have e1 : (a - (1 / 20) * a) * ((99 : ℝ) / 100) - (1 / 20) * a * 1
        ≤ (Work.Kernels.DeltaFun zz * Work.Kernels.E4Fun τ ^ 3).re := by
      have hc : 0 ≤ a - (1 / 20) * a := by linarith
      nlinarith [hA, hWτ_re, hWτ_norm, hc]
    have e2 : (b - (1 / 20) * b) * 1 - (1 / 20) * b * 5
        ≤ (-(Work.Kernels.DeltaFun τ) * Work.Kernels.E4Fun zz ^ 3).re := by
      have hc : 0 ≤ b - (1 / 20) * b := by linarith
      nlinarith [hB, hWz_re, hWz_norm, hc]
    linarith [e1, e2, ha0, hb0]
  have hfinal : (1 / 2) * (a + b)
      ≤ ‖Work.Kernels.DeltaFun zz * Work.Kernels.E4Fun τ ^ 3
          - Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun zz ^ 3‖ :=
    le_trans hmain (Complex.re_le_norm _)
  rw [delta_mul_j_sub τ zz]
  exact hfinal

end Work.CKFinal.LineDecay
