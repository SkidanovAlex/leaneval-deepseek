import Mathlib

/-!
# The inequality `‖α‖ ≤ ‖1 - exp(2πi α)‖` on the half-window `|Im α| < Re α ≤ 1/2`

We prove that for a complex number `α` with `|α.im| < α.re` and `α.re ≤ 1/2` one has
`‖α‖ ≤ ‖1 - exp(2 * π * I * α)‖`.

Writing `x = α.re`, `y = α.im`, `t = exp (-(2π y))`, the modulus identity
`‖1 - exp(2πi α)‖^2 = (1 - t)^2 + 4 t sin(π x)^2` reduces the claim to the real
inequality `x^2 + y^2 ≤ (1 - t)^2 + 4 t sin(π x)^2`, which is proved by splitting
on whether `y ≤ 1/4`.
-/

namespace Work.PertCrux

/-- The squared modulus of `1 - exp (2 * π * I * α)` in terms of the real and
imaginary parts of `α`. -/
private lemma normSq_one_sub_exp (α : ℂ) :
    Complex.normSq (1 - Complex.exp (2 * Real.pi * Complex.I * α))
      = (1 - Real.exp (-(2 * Real.pi * α.im)))^2
        + 4 * Real.exp (-(2 * Real.pi * α.im)) * (Real.sin (Real.pi * α.re))^2 := by
  have hzre : (2 * Real.pi * Complex.I * α).re = -(2 * Real.pi * α.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  have hzim : (2 * Real.pi * Complex.I * α).im = 2 * Real.pi * α.re := by
    simp [Complex.mul_re, Complex.mul_im]
  have hEre : (Complex.exp (2 * Real.pi * Complex.I * α)).re
      = Real.exp (-(2 * Real.pi * α.im)) * Real.cos (2 * Real.pi * α.re) := by
    rw [Complex.exp_re, hzre, hzim]
  have hEim : (Complex.exp (2 * Real.pi * Complex.I * α)).im
      = Real.exp (-(2 * Real.pi * α.im)) * Real.sin (2 * Real.pi * α.re) := by
    rw [Complex.exp_im, hzre, hzim]
  have hcos : Real.cos (2 * Real.pi * α.re) = 1 - 2 * Real.sin (Real.pi * α.re)^2 := by
    rw [mul_assoc]; exact Real.cos_two_mul_eq_one_sub (Real.pi * α.re)
  have hsq : Complex.normSq (1 - Complex.exp (2 * Real.pi * Complex.I * α))
      = 1 - 2 * Real.exp (-(2 * Real.pi * α.im)) * Real.cos (2 * Real.pi * α.re)
        + Real.exp (-(2 * Real.pi * α.im))^2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      hEre, hEim]
    linear_combination (Real.exp (-(2 * Real.pi * α.im))^2) *
      Real.sin_sq_add_cos_sq (2 * Real.pi * α.re)
  rw [hsq, hcos]; ring

/-- The auxiliary real inequality. -/
private lemma real_ineq (x y : ℝ) (h1 : |y| < x) (h2 : x ≤ 1 / 2) :
    x^2 + y^2 ≤ (1 - Real.exp (-(2 * Real.pi * y)))^2
      + 4 * Real.exp (-(2 * Real.pi * y)) * (Real.sin (Real.pi * x))^2 := by
  have hx0 : 0 < x := lt_of_le_of_lt (abs_nonneg y) h1
  have hy2 : y^2 < x^2 := by
    have h : |y|^2 < x^2 := by nlinarith [h1, abs_nonneg y]
    rwa [sq_abs] at h
  have hexp32 : 4 < Real.exp (3 / 2) := by
    have h : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    have h2' : (3 : ℝ) / 2 ≤ Real.exp (1 / 2) := by
      have := Real.add_one_le_exp (1 / 2); linarith
    nlinarith [Real.exp_one_gt_d9, h2', Real.exp_pos (1 / 2)]
  have hexp2lt8 : Real.exp 2 < 8 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  by_cases hy : y ≤ 1 / 4
  · -- Case `y ≤ 1/4`: the term `4 t sin(π x)^2` alone covers `x^2 + y^2`.
    have hle : 2 * Real.pi * y ≤ 2 := by
      have h1' : 2 * Real.pi * y ≤ 2 * Real.pi * (1 / 4) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      nlinarith [h1', Real.pi_lt_four]
    have hexp8 : Real.exp (2 * Real.pi * y) < 8 := by
      have h2' : Real.exp (2 * Real.pi * y) ≤ Real.exp 2 := Real.exp_le_exp.mpr hle
      linarith
    have ht : (1 / 8 : ℝ) ≤ Real.exp (-(2 * Real.pi * y)) := by
      rw [Real.exp_neg]
      simpa using one_div_le_one_div_of_le (Real.exp_pos (2 * Real.pi * y)) hexp8.le
    have hsin : (2 * x)^2 ≤ (Real.sin (Real.pi * x))^2 := by
      have hmul := Real.mul_le_sin (x := Real.pi * x) (by positivity)
        (by nlinarith [h2, Real.pi_pos])
      have h' : 2 * x ≤ Real.sin (Real.pi * x) := by
        have he : (2 / Real.pi) * (Real.pi * x) = 2 * x := by field_simp
        rwa [he] at hmul
      exact pow_le_pow_left₀ (by positivity) h' 2
    have hsin0 : 0 ≤ (Real.sin (Real.pi * x))^2 := sq_nonneg _
    have hkey : 2 * x^2 ≤ 4 * Real.exp (-(2 * Real.pi * y)) * (Real.sin (Real.pi * x))^2 := by
      have hA : 4 * (1 / 8 : ℝ) * (Real.sin (Real.pi * x))^2
          ≤ 4 * Real.exp (-(2 * Real.pi * y)) * (Real.sin (Real.pi * x))^2 := by
        apply mul_le_mul_of_nonneg_right _ hsin0
        nlinarith [ht]
      have hB : 2 * x^2 ≤ 4 * (1 / 8 : ℝ) * (Real.sin (Real.pi * x))^2 := by nlinarith [hsin]
      linarith [hA, hB]
    have hxy : x^2 + y^2 ≤ 2 * x^2 := by nlinarith [hy2]
    nlinarith [hxy, hkey, sq_nonneg (1 - Real.exp (-(2 * Real.pi * y)))]
  · -- Case `1/4 < y`: the term `(1 - t)^2` alone covers `x^2 + y^2`.
    have hy' : 1 / 4 < y := not_le.mp hy
    have h3 : (3 : ℝ) / 2 < 2 * Real.pi * y := by
      have h1' : 2 * Real.pi * (1 / 4) < 2 * Real.pi * y :=
        mul_lt_mul_of_pos_left hy' (by positivity)
      nlinarith [h1', Real.pi_gt_three]
    have hexp4 : 4 < Real.exp (2 * Real.pi * y) := by
      have := Real.exp_lt_exp.mpr h3
      linarith
    have ht : Real.exp (-(2 * Real.pi * y)) < 1 / 4 := by
      rw [Real.exp_neg]
      simpa using one_div_lt_one_div_of_lt (a := (4 : ℝ)) (by norm_num) hexp4
    have hxy : x^2 + y^2 < 1 / 2 := by
      have hx2 : x^2 ≤ 1 / 4 := by
        have := pow_le_pow_left₀ hx0.le h2 2; norm_num at this; linarith
      nlinarith [hx2, hy2]
    have h1t : (3 / 4 : ℝ) < 1 - Real.exp (-(2 * Real.pi * y)) := by linarith
    have hsq : (9 / 16 : ℝ) ≤ (1 - Real.exp (-(2 * Real.pi * y)))^2 := by nlinarith [h1t]
    have hnonneg : 0 ≤ 4 * Real.exp (-(2 * Real.pi * y)) * (Real.sin (Real.pi * x))^2 := by
      positivity
    linarith [hxy, hsq, hnonneg]

theorem norm_alpha_le_norm_one_sub_exp {α : ℂ} (h1 : |α.im| < α.re)
    (h2 : α.re ≤ 1 / 2) :
    ‖α‖ ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
  have hsqα : ‖α‖^2 = α.re^2 + α.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsqE : ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖^2
      = (1 - Real.exp (-(2 * Real.pi * α.im)))^2
        + 4 * Real.exp (-(2 * Real.pi * α.im)) * (Real.sin (Real.pi * α.re))^2 := by
    rw [Complex.sq_norm]; exact normSq_one_sub_exp α
  have hreal : α.re^2 + α.im^2 ≤ (1 - Real.exp (-(2 * Real.pi * α.im)))^2
        + 4 * Real.exp (-(2 * Real.pi * α.im)) * (Real.sin (Real.pi * α.re))^2 :=
    real_ineq α.re α.im h1 h2
  have hsq : ‖α‖^2 ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖^2 := by
    rw [hsqα, hsqE]; exact hreal
  have := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _)] using this

end Work.PertCrux
