import Mathlib
import Submission.Work.EQ.SqrtNearOne

namespace Work.EQ.FanSep

open Complex
open Work.EQ

noncomputable section

/-- The principal square root `z^(1/2)` (`z ≠ 0`) has nonnegative real part:
writing `z = |z| e^{iθ}` with `θ = arg z ∈ (-π, π]`, the real part is
`√|z| cos(θ/2)` and `θ/2 ∈ (-π/2, π/2]`. -/
lemma cpow_half_re_nonneg_aux (z : ℂ) (hz : z ≠ 0) : 0 ≤ (z ^ (1 / 2 : ℂ)).re := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hre : (Complex.log z * (1 / 2 : ℂ)).re = Real.log ‖z‖ / 2 := by
    rw [hhalf, Complex.mul_re, Complex.log_re, Complex.log_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have him : (Complex.log z * (1 / 2 : ℂ)).im = z.arg / 2 := by
    rw [hhalf, Complex.mul_im, Complex.log_re, Complex.log_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    ring
  rw [hre, him]
  apply mul_nonneg (Real.exp_nonneg _)
  apply Real.cos_nonneg_of_mem_Icc
  rw [Set.mem_Icc]
  constructor
  · have h1 := Complex.neg_pi_lt_arg z
    linarith
  · have h2 := Complex.arg_le_pi z
    linarith

/-- Algebraic factorisation behind the principal-square-root step: for `D ≠ 0`,
`(D · (1 + (Q₂/D)²)^{1/2})² = D² + Q₂²`. -/
lemma sq_mul_sqHalf_eq_aux {D Q2 : ℂ} (hD : D ≠ 0) :
    (D * sqHalf ((Q2 / D) ^ 2)) ^ 2 = D ^ 2 + Q2 ^ 2 := by
  rw [mul_pow, sqHalf_sq]
  field_simp

/-- If `0 < D.re`, `|D.im| ≤ D.re/2` and `‖Q₂‖ ≤ ‖D‖/2`, then the product
`D * sqHalf ((Q₂/D)²)` has positive real part; hence it is *the* principal
square root of `D² + Q₂²`.  This is the analytic heart of the second claim. -/
lemma re_mul_sqHalf_pos_aux {D Q2 : ℂ} (hD : D ≠ 0) (hre : 0 < D.re)
    (him : |D.im| ≤ D.re / 2) (hQ2 : ‖Q2‖ ≤ ‖D‖ / 2) :
    0 < (D * sqHalf ((Q2 / D) ^ 2)).re := by
  set w : ℂ := Q2 / D with hwdef
  set S : ℂ := sqHalf (w ^ 2) with hSdef
  have hDnorm_pos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hw : ‖w‖ ≤ 1 / 2 := by
    rw [hwdef, norm_div, div_le_iff₀ hDnorm_pos]
    linarith
  have hlt : ‖w ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [hw, norm_nonneg w]
  have hSre : 0 < S.re := hSdef ▸ sqHalf_re_pos hlt
  have hS2 : (3 : ℝ) / 4 ≤ (S ^ 2).re := by
    rw [hSdef, sqHalf_sq]
    have hle : ‖w ^ 2‖ ≤ 1 / 4 := by rw [norm_pow]; nlinarith [hw, norm_nonneg w]
    have habs := abs_le.mp (Complex.abs_re_le_norm (w ^ 2))
    simp only [Complex.add_re, Complex.one_re]
    linarith [habs.1]
  have hsq_lt : S.im ^ 2 < S.re ^ 2 := by
    have hpow : (S ^ 2).re = S.re ^ 2 - S.im ^ 2 := by
      rw [pow_two, Complex.mul_re]; ring
    nlinarith [hS2]
  have hSabs : |S.im| < S.re := by
    have := (sq_lt_sq.mp hsq_lt)
    rwa [abs_of_pos hSre] at this
  have hchain : |D.im| * |S.im| < D.re * S.re := by
    have hSnn : 0 ≤ |S.im| := abs_nonneg _
    have hstep1 : |D.im| * |S.im| ≤ (D.re / 2) * |S.im| :=
      mul_le_mul_of_nonneg_right him hSnn
    have hstep2 : (D.re / 2) * |S.im| < (D.re / 2) * S.re :=
      mul_lt_mul_of_pos_left hSabs (by linarith)
    have hstep3 : (D.re / 2) * S.re < D.re * S.re := by nlinarith [hre, hSre]
    linarith
  have h2 : D.im * S.im ≤ |D.im| * |S.im| := by
    rw [← abs_mul]; exact le_abs_self _
  rw [Complex.mul_re, hSdef] at *
  linarith

/-- Quantitative inversion bound for `sqHalf`: for `‖z‖ ≤ 1/4`,
`‖(sqHalf z)⁻¹ - 1‖ ≤ 2‖z‖`.  (Apply with `z = w²`: `‖w‖ ≤ 1/2`.) -/
lemma norm_inv_sqHalf_sub_one_le_aux (z : ℂ) (hz : ‖z‖ ≤ 1 / 4) :
    ‖(sqHalf z)⁻¹ - 1‖ ≤ 2 * ‖z‖ := by
  have hzlt : ‖z‖ < 1 := by linarith
  have hS1 : sqHalf z - 1 = z / (sqHalf z + 1) := sqHalf_sub_one hzlt
  have h2 : (1 : ℝ) / 2 ≤ ‖sqHalf z‖ := by
    have hsq : ‖sqHalf z‖ ^ 2 = ‖1 + z‖ := by
      rw [← norm_pow]
      congr 1
      exact sqHalf_sq z
    have h3 : 1 - ‖z‖ ≤ ‖1 + z‖ := by
      have := norm_sub_le (1 + z) z
      simp at this
      linarith
    nlinarith [norm_nonneg (sqHalf z)]
  have hSne : sqHalf z ≠ 0 := by
    intro h
    have := h2
    rw [h] at this
    norm_num at this
  have hkey : (sqHalf z)⁻¹ - 1 = -(z) / (sqHalf z * (sqHalf z + 1)) := by
    rw [show (sqHalf z)⁻¹ - 1 = -(sqHalf z - 1) / sqHalf z by field_simp; ring, hS1]
    field_simp
  rw [hkey, norm_div, norm_neg, norm_mul]
  have hprod : (1 : ℝ) / 2 ≤ ‖sqHalf z‖ * ‖sqHalf z + 1‖ := by
    have h1 : 1 ≤ ‖sqHalf z + 1‖ := norm_sqHalf_add_one_ge_one hzlt
    nlinarith [norm_nonneg (sqHalf z), norm_nonneg (sqHalf z + 1)]
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖sqHalf z‖ * ‖sqHalf z + 1‖)]
  nlinarith [norm_nonneg z]

theorem sqrt_step :
    (∀ z : ℂ, z ≠ 0 → 0 ≤ (z ^ (1 / 2 : ℂ)).re) ∧
    (∀ {D Q2 : ℂ}, D ≠ 0 → 0 < D.re → |D.im| ≤ D.re / 2 → ‖Q2‖ ≤ ‖D‖ / 2 →
      (D ^ 2 + Q2 ^ 2) ^ (1 / 2 : ℂ) = D * sqHalf ((Q2 / D) ^ 2)) ∧
    (∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ‖(sqHalf (w ^ 2))⁻¹ - 1‖ ≤ 2 * ‖w‖ ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact cpow_half_re_nonneg_aux z hz
  · intro D Q2 hD hre him hQ2
    let S := sqHalf ((Q2 / D) ^ 2)
    have hsq : (D * S) ^ 2 = D ^ 2 + Q2 ^ 2 := sq_mul_sqHalf_eq_aux hD
    have hpos : 0 < (D * S).re := re_mul_sqHalf_pos_aux hD hre him hQ2
    have h := Complex.sq_cpow_two_inv hpos
    rw [hsq] at h
    rwa [show (2 : ℂ)⁻¹ = (1 / 2 : ℂ) by norm_num] at h
  · intro w hw
    have hwnorm : ‖w ^ 2‖ ≤ 1 / 4 := by
      rw [norm_pow]
      nlinarith [hw, norm_nonneg w]
    have h := norm_inv_sqHalf_sub_one_le_aux (w ^ 2) hwnorm
    rwa [norm_pow] at h

end

end Work.EQ.FanSep
