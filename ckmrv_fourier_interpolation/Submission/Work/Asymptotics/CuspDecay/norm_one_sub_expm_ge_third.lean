import Mathlib

namespace Work.Asymptotics.CuspDecay

/-- **Exact identity for the squared modulus.**
With `r := e^{2πy}` (where `w = x + iy`) one has
`‖1 - e^{-2πiw}‖² = (1-r)² + 4 r sin²(πx)`. -/
lemma norm_sq_exp_identity (w : ℂ) :
    ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖^2
      = (1 - Real.exp (2 * Real.pi * w.im))^2
        + 4 * Real.exp (2 * Real.pi * w.im) * Real.sin (Real.pi * w.re)^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))).re
      = 1 - Real.exp (2 * Real.pi * w.im) * Real.cos (2 * Real.pi * w.re) := by
    simp [Complex.sub_re, Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Real.cos_neg]
  have him : (1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))).im
      = Real.exp (2 * Real.pi * w.im) * Real.sin (2 * Real.pi * w.re) := by
    simp [Complex.sub_im, Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Real.sin_neg]
  rw [hre, him]
  have hsc := Real.sin_sq_add_cos_sq (2 * Real.pi * w.re)
  have hcos : Real.cos (2 * Real.pi * w.re) = 1 - 2 * Real.sin (Real.pi * w.re)^2 := by
    rw [show 2 * Real.pi * w.re = 2 * (Real.pi * w.re) by ring, Real.cos_two_mul_eq_one_sub]
  linear_combination (Real.exp (2 * Real.pi * w.im)^2) * hsc - (2 * Real.exp (2 * Real.pi * w.im)) * hcos

/-- `sin²(πx) ≥ 4x²` on `|x| ≤ 1/2`. -/
lemma four_mul_sq_le_sin_sq (x : ℝ) (hx : |x| ≤ 1 / 2) :
    4 * x^2 ≤ Real.sin (Real.pi * x)^2 := by
  have hpx : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, hx]
  have h2 := Real.mul_abs_le_abs_sin hpx
  rw [abs_mul, abs_of_pos Real.pi_pos] at h2
  have hsimp : 2 / Real.pi * (Real.pi * |x|) = 2 * |x| := by field_simp
  rw [hsimp] at h2
  have h2' : (2 * |x|)^2 ≤ Real.sin (Real.pi * x)^2 := by
    rw [← sq_abs (Real.sin (Real.pi * x))]
    exact pow_le_pow_left₀ (by positivity) h2 2
  rw [mul_pow, sq_abs] at h2'
  linarith [h2']

/-- For `-2 ≤ t ≤ 0` one has `-t/3 ≤ 1 - e^t`. -/
lemma one_sub_exp_ge_neg_third (t : ℝ) (h0 : t ≤ 0) (h2 : -2 ≤ t) :
    -t / 3 ≤ 1 - Real.exp t := by
  set s := -t with hs
  have hs0 : 0 ≤ s := by linarith
  have hs2 : s ≤ 2 := by linarith
  have ht : Real.exp t = (Real.exp s)⁻¹ := by
    rw [show t = -s by linarith [hs], Real.exp_neg]
  have hexp : 1 + s ≤ Real.exp s := by have := Real.add_one_le_exp s; linarith
  have h1s : (0:ℝ) < 1 + s := by linarith
  have hle : (Real.exp s)⁻¹ ≤ (1 + s)⁻¹ := by
    rw [inv_le_inv₀ (Real.exp_pos s) h1s]; exact hexp
  have h1 : 1 - (1 + s)⁻¹ ≤ 1 - Real.exp t := by rw [ht]; linarith
  have h2' : s / (1 + s) = 1 - (1 + s)⁻¹ := by
    rw [eq_sub_iff_add_eq]; field_simp; try ring
  have h3 : s / 3 ≤ s / (1 + s) := div_le_div_of_nonneg_left hs0 h1s (by linarith)
  rw [show -t / 3 = s / 3 by rw [hs]]
  linarith [h1, h2', h3]

/-- For `t ≥ -2` one has `e^t ≥ 1/9`. -/
lemma exp_ge_ninth_of_ge_neg_two (t : ℝ) (ht : -2 ≤ t) : (1:ℝ)/9 ≤ Real.exp t := by
  have hmono : Real.exp (-2) ≤ Real.exp t := Real.exp_le_exp.mpr ht
  have hlt : Real.exp (2:ℝ) < 9 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have h : (1:ℝ)/9 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]
    rw [inv_le_inv₀ (by norm_num : (0:ℝ) < 9) (Real.exp_pos 2)]
    exact le_of_lt hlt
  linarith

/-- For `t ≤ -2` one has `e^t ≤ 1/4`. -/
lemma exp_le_quarter_of_le_neg_two (t : ℝ) (ht : t ≤ -2) : Real.exp t ≤ (1:ℝ)/4 := by
  have hmono : Real.exp t ≤ Real.exp (-2) := Real.exp_le_exp.mpr ht
  have hgt : (4:ℝ) < Real.exp (2:ℝ) := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]
  have h : Real.exp (-2) ≤ (1:ℝ)/4 := by
    rw [Real.exp_neg, one_div]
    rw [inv_le_inv₀ (Real.exp_pos 2) (by norm_num : (0:ℝ) < 4)]
    exact le_of_lt hgt
  linarith

/-- **The exponential `1 - e^{-2πiw}` dominates `‖w‖/3` on the nearest-lattice strip.**

For `w = x + iy` with `|x| ≤ 1/2` and `‖w‖ ≤ 2` one has
`‖1 - e^{-2πiw}‖ ≥ ‖w‖/3`.

With `r := e^{2πy}` one has the exact identity
`‖1 - e^{-2πiw}‖² = (1-r)² + 4 r sin²(πx)`.
* If `y ≥ 0` then `r ≥ 1`, `r - 1 = e^{2πy} - 1 ≥ 2πy`, and `sin²(πx) ≥ 4x²`,
  so `‖1 - e^{-2πiw}‖² ≥ 4π²y² + 16x² ≥ 16(x² + y²) = 16‖w‖²`.
* If `y < 0`, put `s := 2π|y|`.  For `s ≥ 2` the first term alone gives
  `(1-r)² ≥ 9/16 ≥ (1/9)‖w‖²`; for `s < 2` one has `1 - e^{-2πy} ≥ s/3` and
  `r ≥ 1/9`, so `‖1 - e^{-2πiw}‖² ≥ y²/9 + x²/9 = (1/9)‖w‖²`. -/
theorem norm_one_sub_expm_ge_third (w : ℂ) (hre : |w.re| ≤ 1 / 2) (hn : ‖w‖ ≤ 2) :
    (1 / 3) * ‖w‖ ≤ ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ := by
  have hsin4 : 4 * w.re^2 ≤ Real.sin (Real.pi * w.re)^2 := four_mul_sq_le_sin_sq w.re hre
  have hx2 : w.re^2 ≤ 1/4 := by nlinarith [abs_nonneg w.re, hre, sq_abs w.re]
  have hy2 : w.im^2 ≤ 4 := by
    have h := Complex.abs_im_le_norm w
    nlinarith [abs_nonneg w.im, h, hn, sq_abs w.im]
  have hmainsq : (w.re^2 + w.im^2) / 9 ≤
      ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖^2 := by
    rw [norm_sq_exp_identity]
    set R := Real.exp (2 * Real.pi * w.im) with hR
    have hRpos : 0 ≤ R := by rw [hR]; exact le_of_lt (Real.exp_pos _)
    by_cases hy : 0 ≤ w.im
    · have hR1 : 1 ≤ R := by rw [hR]; exact Real.one_le_exp (by positivity)
      have hge : 2 * Real.pi * w.im ≤ R - 1 := by
        have h := Real.add_one_le_exp (2 * Real.pi * w.im)
        rw [← hR] at h; linarith
      have hbase : 0 ≤ 2 * Real.pi * w.im := by positivity
      have hA : (2 * Real.pi * w.im)^2 ≤ (1 - R)^2 := by
        rw [show (1 - R)^2 = (R - 1)^2 by ring]
        exact pow_le_pow_left₀ hbase hge 2
      have hB : 16 * w.re^2 ≤ 4 * R * Real.sin (Real.pi * w.re)^2 := by
        have h4 : 0 ≤ Real.sin (Real.pi * w.re)^2 := sq_nonneg _
        have h1 : Real.sin (Real.pi * w.re)^2 ≤ R * Real.sin (Real.pi * w.re)^2 := by
          simpa using mul_le_mul_of_nonneg_right hR1 h4
        nlinarith [h1, hsin4]
      have hlow : (w.re^2 + w.im^2) / 9 ≤ (2 * Real.pi * w.im)^2 + 16 * w.re^2 := by
        have hp2 : (4:ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
        nlinarith [hp2, sq_nonneg w.im, sq_nonneg w.re]
      linarith [hA, hB, hlow]
    · have hy' : w.im < 0 := not_le.mp hy
      by_cases hs : -(2 * Real.pi * w.im) ≤ 2
      · have ht2 : -2 ≤ 2 * Real.pi * w.im := by linarith
        have ht0 : 2 * Real.pi * w.im ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt hy')
        have hge1 : -(2 * Real.pi * w.im) / 3 ≤ 1 - R := by
          rw [hR]; exact one_sub_exp_ge_neg_third (2 * Real.pi * w.im) ht0 ht2
        have hgnn : 0 ≤ -(2 * Real.pi * w.im) / 3 := by linarith
        have hA : w.im^2 / 9 ≤ (1 - R)^2 := by
          have hsq : (-(2 * Real.pi * w.im) / 3)^2 ≤ (1 - R)^2 := pow_le_pow_left₀ hgnn hge1 2
          have hcmp : w.im^2 / 9 ≤ (-(2 * Real.pi * w.im) / 3)^2 := by
            have hp2 : (1:ℝ) ≤ 4 * Real.pi^2 := by nlinarith [Real.pi_gt_three]
            nlinarith [hp2, sq_nonneg w.im]
          linarith [hsq]
        have hB : w.re^2 / 9 ≤ 4 * R * Real.sin (Real.pi * w.re)^2 := by
          have hR9 : (1:ℝ)/9 ≤ R := by
            rw [hR]; exact exp_ge_ninth_of_ge_neg_two (2 * Real.pi * w.im) ht2
          have h4 : 0 ≤ Real.sin (Real.pi * w.re)^2 := sq_nonneg _
          have h1 : (1:ℝ)/9 * Real.sin (Real.pi * w.re)^2 ≤ R * Real.sin (Real.pi * w.re)^2 := by
            simpa using mul_le_mul_of_nonneg_right hR9 h4
          nlinarith [h1, hsin4]
        linarith [hA, hB]
      · have ht2 : 2 * Real.pi * w.im ≤ -2 := by have h := not_le.mp hs; linarith
        have hR4 : R ≤ 1/4 := by rw [hR]; exact exp_le_quarter_of_le_neg_two _ ht2
        have hA : (9:ℝ)/16 ≤ (1 - R)^2 := by
          have h3 : (3:ℝ)/4 ≤ 1 - R := by linarith
          nlinarith [h3]
        have hpos : 0 ≤ 4 * R * Real.sin (Real.pi * w.re)^2 := by
          apply mul_nonneg
          · exact mul_nonneg (by norm_num) hRpos
          · exact sq_nonneg _
        have hsup : (w.re^2 + w.im^2) / 9 ≤ 17/36 := by nlinarith [hx2, hy2]
        have hnum : (17:ℝ)/36 ≤ 9/16 := by norm_num
        linarith [hA, hsup, hnum, hpos]
  have hsq1 : ((1/3) * ‖w‖)^2 = (w.re^2 + w.im^2) / 9 := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  have hmain : ((1/3) * ‖w‖)^2 ≤ ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖^2 := by
    rw [hsq1]; exact hmainsq
  have h3 : (0:ℝ) ≤ (1/3) * ‖w‖ := by positivity
  have h4 : (0:ℝ) ≤ ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ := norm_nonneg _
  have hh := Real.sqrt_le_sqrt hmain
  rwa [Real.sqrt_sq h3, Real.sqrt_sq h4] at hh

end Work.Asymptotics.CuspDecay
