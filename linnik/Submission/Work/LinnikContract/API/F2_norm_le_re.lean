import Mathlib
import Submission.Work.LinnikContract.API.norm_sinh_sq
import Submission.Work.LinnikContract.API.F2_eq_exp_sinh

namespace Work.LinnikContract.API

/-- The elementary inequality behind the estimate: for `u > 0` and any real `v`,
`(sinh²u + sin²v)/(u²+v²) ≤ sinh²u/u²`.
Cross-multiplying, this is `u² sin²v ≤ v² sinh²u`, which follows from
`sin²v ≤ v²` and `u ≤ sinh u` (so `u² ≤ sinh²u`). -/
private lemma sinh_ratio_le (u v : ℝ) (hu : 0 < u) :
    (Real.sinh u ^ 2 + Real.sin v ^ 2) / (u ^ 2 + v ^ 2) ≤ Real.sinh u ^ 2 / u ^ 2 := by
  have hu2 : (0:ℝ) < u^2 := by positivity
  have huv : (0:ℝ) < u^2 + v^2 := by positivity
  rw [div_le_div_iff₀ huv hu2]
  have hsin : Real.sin v ^ 2 ≤ v ^ 2 := Real.sin_sq_le_sq
  have hsinh : u ≤ Real.sinh u := Real.self_le_sinh_iff.mpr (le_of_lt hu)
  have hsinh0 : 0 ≤ Real.sinh u := le_of_lt (Real.sinh_pos_iff.mpr hu)
  have hsinhsq : u^2 ≤ Real.sinh u^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsinh) (add_nonneg hsinh0 hu.le)]
  have h1 : u^2 * Real.sin v ^ 2 ≤ u^2 * v^2 := mul_le_mul_of_nonneg_left hsin (by positivity)
  have h2 : u^2 * v^2 ≤ Real.sinh u^2 * v^2 := mul_le_mul_of_nonneg_right hsinhsq (by positivity)
  nlinarith [h1, h2]

/-- Closed form for the modulus of HB's test function: for `K > 0`, `Re z > 0`,
`‖F₂(z)‖ = K² e^{-K Re z} (sinh²(K Re z / 2) + sin²(K Im z / 2)) / ((K Re z / 2)² + (K Im z / 2)²)`.
Obtained by taking norms in `F2_eq_exp_sinh` and applying `norm_sinh_sq`. -/
private lemma F2_norm_eq (K : ℝ) (hK : 0 < K) (z : ℂ) (hz : 0 < z.re) :
    ‖Work.LinnikContract.F2 K z‖ = K^2 * Real.exp (-(K * z.re)) *
      ((Real.sinh (K * z.re / 2) ^ 2 + Real.sin (K * z.im / 2) ^ 2) /
      ((K * z.re / 2) ^ 2 + (K * z.im / 2) ^ 2)) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hC := F2_eq_exp_sinh K hK0 z hz0
  have hAre : ((K:ℂ)*z/2).re = K*z.re/2 := by
    have : (K:ℂ)*z/2 = ((K/2 : ℝ) : ℂ) * z := by push_cast; ring
    rw [this, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; ring
  have hAim : ((K:ℂ)*z/2).im = K*z.im/2 := by
    have : (K:ℂ)*z/2 = ((K/2 : ℝ) : ℂ) * z := by push_cast; ring
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul]; ring
  have hsinh : (‖Complex.sinh ((K:ℂ)*z/2)‖ / ‖(K:ℂ)*z/2‖)^2 =
      (Real.sinh (K*z.re/2)^2 + Real.sin (K*z.im/2)^2) /
      ((K*z.re/2)^2 + (K*z.im/2)^2) := by
    rw [div_pow, norm_sinh_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hAre, hAim]
    ring
  rw [hC]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_exp]
  rw [show ‖(K:ℂ)‖^2 = K^2 from by rw [show ‖(K:ℂ)‖ = |K| from RCLike.norm_ofReal K, sq_abs],
      show (-(K:ℂ)*z).re = -(K*z.re) from by simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im],
      hsinh]

/-- `‖F₂(z)‖ ≤ ‖F₂(Re z)‖` for `Re z > 0`: this is the inequality that lets every estimate of
HB §13 be phrased on the real axis.

Prover notes: with `x = z.re > 0` and `w = K*z`, `z = K⁻¹w`, `(1 - e^{-Kz})/z = K*e^{-w/2}*sinh(w/2)/(w/2)`,
so `‖F2 K z‖ = (K*e^{-u}*…)²` with `u = K x/2`; using `‖sinh(u+iv)‖² = sinh²u + sin²v`
(`Complex.sinh_sq_add_sin_sq`-style, or `Complex.norm_sinh`) the claim reduces to
`u² sin²v ≤ v² sinh²u`, which follows from `Real.abs_sin_le_abs` and `Real.self_le_sinh`.
No `native_decide`. -/
theorem F2_norm_le_re (K : ℝ) (hK : 0 < K) (z : ℂ) (hz : 0 < z.re) :
    ‖Work.LinnikContract.F2 K z‖ ≤ ‖Work.LinnikContract.F2 K ((z.re : ℂ))‖ := by
  have hzr : 0 < ((z.re : ℂ)).re := by simpa using hz
  have h1 := F2_norm_eq K hK z hz
  have h2 : ‖Work.LinnikContract.F2 K ((z.re : ℂ))‖ = K^2 * Real.exp (-(K * z.re)) *
      (Real.sinh (K * z.re / 2) ^ 2 / (K * z.re / 2) ^ 2) := by
    rw [F2_norm_eq K hK ((z.re : ℂ)) hzr]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    norm_num
  rw [h1, h2]
  have hu : (0:ℝ) < K * z.re / 2 := by positivity
  have hc : (0:ℝ) < K^2 * Real.exp (-(K * z.re)) := by positivity
  exact mul_le_mul_of_nonneg_left (sinh_ratio_le (K*z.re/2) (K*z.im/2) hu) hc.le

end Work.LinnikContract.API
