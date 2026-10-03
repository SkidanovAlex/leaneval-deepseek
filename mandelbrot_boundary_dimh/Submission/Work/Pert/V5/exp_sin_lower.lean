import Mathlib

/-!
# `Work.Pert.V5.exp_sin_lower`

For `w : ℂ` with `|Re w| ≤ 1/2` and `D > 0`, `D ≤ ‖w‖`:

  `4 D exp (π Im w) ≤ ‖1 - exp (-(2π i w))‖`.

**Route.**  Write `a = Re w`, `b = Im w` and `u = exp (2π b)`.  Since
`-(2π i w) = 2π b - 2π a i`, one has

  `exp (-(2π i w)) = u · (cos (2π a) - sin (2π a) i)`,

so `Re (exp (-(2π i w))) = u cos (2π a)` and `‖exp (-(2π i w))‖ = u`.  Hence

  `‖1 - exp (-(2π i w))‖² = 1 - 2 u cos (2π a) + u² = (1 - u)² + 2 u (1 - cos (2π a))`.

Two elementary estimates finish:

* `(1 - u)² ≥ 16 b² u`,  i.e. `4 (π b)² exp (2 π b) ≤ (1 - exp (2 π b))²`, which follows from
  `|sinh x| = sinh |x| ≥ |x|` and `π ≥ 2` (`four_mul_sq_mul_exp_le`, `key_real`);
* `2 u (1 - cos (2π a)) ≥ 16 a² u`,  from Mathlib's `Real.cos_le_one_sub_mul_cos_sq`
  applied with `x = 2π a` (`key_cos`), using `|a| ≤ 1/2`.

Adding, and using `D² ≤ ‖w‖² = a² + b²` and `u = (exp (π b))²`, gives
`(4 D exp (π b))² ≤ ‖1 - exp (-(2π i w))‖²`, and both sides are nonnegative.
-/

namespace Work.Pert.V5

/-- For every real `x`, `4 x² exp (2x) ≤ (1 - exp (2x))²`.

Writing `exp (2x) - 1 = 2 exp x sinh x`, the left-hand factor is
`(1 - exp (2x))² = 4 exp (2x) sinh x²`, and `sinh x² ≥ x²` because
`|sinh x| = sinh |x| ≥ |x|`. -/
private lemma four_mul_sq_mul_exp_le (x : ℝ) :
    4 * x ^ 2 * Real.exp (2 * x) ≤ (1 - Real.exp (2 * x)) ^ 2 := by
  have hexp2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  have h1 : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hone : Real.exp (2 * x) - 1 = 2 * Real.exp x * Real.sinh x := by
    rw [Real.sinh_eq, hexp2]; linear_combination h1
  have hsq : (1 - Real.exp (2 * x)) ^ 2 = 4 * Real.exp (2 * x) * Real.sinh x ^ 2 := by
    have h : (1 - Real.exp (2 * x)) = -(Real.exp (2 * x) - 1) := by ring
    rw [h, neg_sq, hone, hexp2]; ring
  have hge : x ^ 2 ≤ Real.sinh x ^ 2 := by
    have h1 : |Real.sinh x| = Real.sinh |x| := Real.abs_sinh x
    have h2 : |x| ≤ Real.sinh |x| := Real.self_le_sinh_iff.mpr (abs_nonneg x)
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ Real.sinh |x| ^ 2 := pow_le_pow_left₀ (abs_nonneg x) h2 2
      _ = Real.sinh x ^ 2 := by rw [← h1, sq_abs]
  rw [hsq]
  have he : (0 : ℝ) < Real.exp (2 * x) := Real.exp_pos _
  nlinarith [hge, he]

/-- Sharpened form used below: `16 b² exp (2π b) ≤ (1 - exp (2π b))²`.

It is `four_mul_sq_mul_exp_le` at `x = π b`, together with `4 ≤ π²`. -/
private lemma key_real (b : ℝ) :
    16 * b ^ 2 * Real.exp (2 * Real.pi * b) ≤ (1 - Real.exp (2 * Real.pi * b)) ^ 2 := by
  have h := four_mul_sq_mul_exp_le (Real.pi * b)
  have harg : 2 * (Real.pi * b) = 2 * Real.pi * b := by ring
  rw [harg] at h
  have hp2 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hE : (0 : ℝ) ≤ Real.exp (2 * Real.pi * b) := (Real.exp_pos _).le
  nlinarith [h, hp2, sq_nonneg b, hE]

/-- For `|a| ≤ 1/2`, `8 a² ≤ 1 - cos (2π a)`.

Mathlib's `Real.cos_le_one_sub_mul_cos_sq` with `x = 2π a` gives
`cos (2π a) ≤ 1 - (2/π²) (2π a)² = 1 - 8 a²`. -/
private lemma key_cos (a : ℝ) (ha : |a| ≤ 1 / 2) :
    8 * a ^ 2 ≤ 1 - Real.cos (2 * Real.pi * a) := by
  have hx : |2 * Real.pi * a| ≤ Real.pi := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
    nlinarith [ha, Real.pi_pos]
  have h := Real.cos_le_one_sub_mul_cos_sq hx
  have h2 : 2 / Real.pi ^ 2 * (2 * Real.pi * a) ^ 2 = 8 * a ^ 2 := by
    field_simp; ring
  rw [h2] at h
  linarith

/-- `‖1 - z‖² = 1 - 2 Re z + ‖z‖²`, through `Complex.sq_norm` and `Complex.normSq_apply`. -/
private lemma norm_sq_one_sub (z : ℂ) : ‖1 - z‖ ^ 2 = 1 - 2 * z.re + ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

theorem exp_sin_lower (w : ℂ) (ha : |w.re| ≤ 1 / 2) {D : ℝ} (hD : 0 < D) (hDw : D ≤ ‖w‖) :
    4 * D * Real.exp (Real.pi * w.im) ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖ := by
  -- Real and imaginary parts of the exponent `-(2π i w)`.
  have hZre : (-(2 * Real.pi * Complex.I * w)).re = 2 * Real.pi * w.im := by
    simp [Complex.mul_re, Complex.mul_im]
  have hZim : (-(2 * Real.pi * Complex.I * w)).im = -(2 * Real.pi * w.re) := by
    simp [Complex.mul_re, Complex.mul_im]
  have hupos : (0 : ℝ) < Real.exp (2 * Real.pi * w.im) := Real.exp_pos _
  -- Real part and modulus of `exp (-(2π i w))`.
  have hEre : (Complex.exp (-(2 * Real.pi * Complex.I * w))).re
      = Real.exp (2 * Real.pi * w.im) * Real.cos (2 * Real.pi * w.re) := by
    rw [Complex.exp_re, hZre, hZim, Real.cos_neg]
  have hEnorm : ‖Complex.exp (-(2 * Real.pi * Complex.I * w))‖
      = Real.exp (2 * Real.pi * w.im) := by
    rw [Complex.norm_exp, hZre]
  -- Exact value of the squared modulus.
  have hsq : ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖ ^ 2
      = (1 - Real.exp (2 * Real.pi * w.im)) ^ 2
        + 2 * Real.exp (2 * Real.pi * w.im) * (1 - Real.cos (2 * Real.pi * w.re)) := by
    rw [norm_sq_one_sub, hEre, hEnorm]; ring
  have hb := key_real w.im
  have hcc := key_cos w.re ha
  have hD2 : D ^ 2 ≤ w.re ^ 2 + w.im ^ 2 := by
    have h : D ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hD.le hDw 2
    have hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rwa [hw] at h
  have huE : Real.exp (2 * Real.pi * w.im) = Real.exp (Real.pi * w.im) ^ 2 := by
    rw [show 2 * Real.pi * w.im = Real.pi * w.im + Real.pi * w.im by ring, Real.exp_add]
    ring
  have hmain : (4 * D * Real.exp (Real.pi * w.im)) ^ 2
      ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * w))‖ ^ 2 := by
    rw [hsq]
    nlinarith [hb, hcc, hD2, hupos, huE]
  have hx0 : (0 : ℝ) ≤ 4 * D * Real.exp (Real.pi * w.im) := by positivity
  have hle := sq_le_sq.mp hmain
  rwa [abs_of_nonneg hx0, abs_of_nonneg (norm_nonneg _)] at hle

end Work.Pert.V5
