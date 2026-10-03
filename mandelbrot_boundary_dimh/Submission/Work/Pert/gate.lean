import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.gate_derivF

/-!
# PERT · `Work.Pert.gate`: Shishikura (A.1.7)(ii) in the `1/32` form

This file proves the lemma `Work.Pert.gate` of the PERT area: on the two gate regions
`Qreg ξ₁ (-ξ₁ + 1/α)` and `Qreg (ξ₁ - 1/α) (-ξ₁)` the lift `F_f = liftF u σ α` of a small
perturbation `f z = z + z(z-σ)u z` of a parabolic germ is a near-translation with the errors
`‖F_f w - (w+1)‖ ≤ 1/32`, `‖F_f'(w) - 1‖ ≤ 1/32`.  The constants are `ξ₁ = 10^6`,
`ε₀ = 10^{-6}`, `ρ₀ = 1`.

The mathematical content, all with room to spare (the estimates below are deliberately crude,
they only have to beat `1/32`):

* `‖σ‖ ≤ 8π‖α‖` from the normalisation `1 - σ u 0 = exp(2πiα)` and `1/2 ≤ ‖u 0‖` (A.1.2);
* the gates keep distance `≥ ξ₁/2` from the lattice `ℤ/α` (that the paper encodes by removing
  `⋃_n T_f^n D_{R₀}`); the proof is the elementary geometry of the two `±45°` cones, and needs
  `InF1 α` (`|Im α| < Re α`);
* hence `‖τ_f(w)‖ = ‖σ/(1 - exp(-2πiαw))‖ ≤ 51·10^{-6} ≪ ρ₀`;
* the Abel-quantity `s = σu(τ)/(1+τu(τ))` and the error
  `E = (1-s-A)/A`, `A = exp(2πiα) = 1 - σu(0)`, satisfy `‖E‖ ≤ 48‖σ‖‖τ‖`;
* writing `1 - s = A(1+E)`, the principal branches give
  `log(1-s) = log A + log(1+E) = 2πiα + log(1+E)`, so
  `F_f(w) - (w+1) = log(1+E)/(2πiα)`, bounded by `(3/2)‖E‖/(2π‖α‖) ≤ 1/32`;
* the derivative formula (A.1.7)(ii) `F_f' - 1 = τ(τ-σ)(u'(τ)-u(τ)²)/((1+τu(τ)-σu(τ))(1+τu(τ)))`
  (proved in `Submission/Work/Pert/gate_derivF.lean`) is then bounded by `O(‖τ‖²)`.

The facts `‖u‖ ≤ 2`, `‖u'‖ ≤ 8` on `ball 0 (1/2)` (Cauchy) and the mean value bound
`‖u 0 - u τ‖ ≤ 8‖τ‖` are derived here, so no derivative hypothesis on `u` is needed.
-/

namespace Work.Pert

open MandelDim
open Complex

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

private lemma exp_neg_pi_div_two_ge_eighth : (1 : ℝ) / 8 ≤ Real.exp (-(Real.pi / 2)) := by
  have hE : Real.exp (Real.pi / 2) ≤ 8 := by
    have h1 : Real.pi / 2 < Real.log 8 := by
      have h2 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      have h3 := Real.log_two_gt_d9
      rw [h2]
      linarith [Real.pi_lt_four, h3]
    have h4 := Real.exp_le_exp.mpr (le_of_lt h1)
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 8)] at h4
  calc (1 : ℝ) / 8 = (8 : ℝ)⁻¹ := by norm_num
    _ ≤ (Real.exp (Real.pi / 2))⁻¹ := (inv_le_inv₀ (by norm_num) (Real.exp_pos _)).mpr hE
    _ = Real.exp (-(Real.pi / 2)) := by rw [Real.exp_neg]

private lemma exp_neg_pi_div_two_le_half : Real.exp (-(Real.pi / 2)) ≤ 1 / 2 := by
  have hE : (2 : ℝ) ≤ Real.exp (Real.pi / 2) := by
    have h1 : Real.log 2 < Real.pi / 2 := by
      linarith [Real.log_two_lt_d9, Real.pi_gt_three]
    have h2 := Real.exp_le_exp.mpr (le_of_lt h1)
    rwa [show Real.exp (Real.log 2) = 2 from Real.exp_log (by norm_num)] at h2
  calc Real.exp (-(Real.pi / 2)) = (Real.exp (Real.pi / 2))⁻¹ := Real.exp_neg _
    _ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hE
    _ = 1 / 2 := by norm_num

private lemma two_le_exp_pi_div_two : (2 : ℝ) ≤ Real.exp (Real.pi / 2) := by
  have h1 : Real.log 2 < Real.pi / 2 := by
    linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have h2 := Real.exp_le_exp.mpr (le_of_lt h1)
  rwa [show Real.exp (Real.log 2) = 2 from Real.exp_log (by norm_num)] at h2

private lemma one_sub_cos_two_pi_ge {x : ℝ} (hx : |x| ≤ 1 / 2) :
    8 * x ^ 2 ≤ 1 - Real.cos (2 * Real.pi * x) := by
  have hsin : 2 * |x| ≤ Real.sin (Real.pi * |x|) := by
    have h1 : 0 ≤ Real.pi * |x| := by positivity
    have h2 : Real.pi * |x| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, abs_nonneg x, hx]
    have h3 := Real.mul_le_sin h1 h2
    have h4 : 2 / Real.pi * (Real.pi * |x|) = 2 * |x| := by field_simp
    rwa [h4] at h3
  have hsq : (2 * |x|) ^ 2 ≤ Real.sin (Real.pi * |x|) ^ 2 := by
    nlinarith [hsin, abs_nonneg x]
  have hsin2 : Real.sin (Real.pi * |x|) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, show Real.pi * -x = -(Real.pi * x) by ring, Real.sin_neg, neg_sq]
  have hcos : 1 - Real.cos (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) ^ 2 := by
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul]
    have := Real.sin_sq (Real.pi * x)
    linarith
  rw [hcos, ← hsin2]
  have h4 : (2 * |x|) ^ 2 = 4 * x ^ 2 := by rw [mul_pow, sq_abs]; ring
  linarith [hsq, h4.le, h4.ge]

private lemma sub_exp_neg_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have hexp : (1 + t) ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h1 : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg]
    calc (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ := (inv_le_inv₀ (Real.exp_pos t) hpos).mpr hexp
      _ = 1 / (1 + t) := by rw [one_div]
  have h2 : t / 2 ≤ 1 - 1 / (1 + t) := by
    have heq : 1 - 1 / (1 + t) = t / (1 + t) := by
      field_simp
      ring
    rw [heq, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hpos]
    nlinarith
  linarith

private lemma exp_two_pi_I_sq (δ : ℂ) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I * δ)‖ ^ 2
      = 1 - 2 * (Real.exp (-(2 * Real.pi * δ.im)) * Real.cos (2 * Real.pi * δ.re))
        + Real.exp (-(2 * Real.pi * δ.im)) ^ 2 := by
  have hre : (2 * Real.pi * Complex.I * δ).re = -(2 * Real.pi * δ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  have him : (2 * Real.pi * Complex.I * δ).im = 2 * Real.pi * δ.re := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.exp_re, Complex.exp_im, hre, him]
  nlinarith [Real.sin_sq (2 * Real.pi * δ.re)]

private lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  rw [Real.exp_neg]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  calc (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).mpr h2
    _ = 1 / 2 := by norm_num

/-- `|y| ≤ |1 - exp (-2πy)|` for `|y| ≤ 1/4`. -/
private lemma abs_y_le_one_sub_exp_neg {y : ℝ} (hy : |y| ≤ 1 / 4) :
    |y| ≤ |1 - Real.exp (-(2 * Real.pi * y))| := by
  rcases le_total 0 y with h | h
  · have hy' : y ≤ 1 / 4 := by rwa [abs_of_nonneg h] at hy
    rcases le_total (2 * Real.pi * y) 1 with ht | ht
    · have ht0 : 0 ≤ 2 * Real.pi * y := by positivity
      have h1 := sub_exp_neg_ge ht0 ht
      have h2 : y ≤ Real.pi * y := by nlinarith [Real.pi_gt_three, h]
      have h3 : |1 - Real.exp (-(2 * Real.pi * y))| = 1 - Real.exp (-(2 * Real.pi * y)) := by
        apply abs_of_nonneg
        have := Real.exp_le_one_iff.mpr (by linarith : -(2 * Real.pi * y) ≤ 0)
        linarith
      rw [h3, abs_of_nonneg h]
      linarith
    · have h3 : Real.exp (-(2 * Real.pi * y)) ≤ Real.exp (-1) :=
        Real.exp_le_exp.mpr (by linarith)
      have h4 : |1 - Real.exp (-(2 * Real.pi * y))| = 1 - Real.exp (-(2 * Real.pi * y)) := by
        apply abs_of_nonneg
        have := Real.exp_le_one_iff.mpr (by linarith : -(2 * Real.pi * y) ≤ 0)
        linarith
      rw [h4, abs_of_nonneg h]
      linarith [h3, exp_neg_one_le_half, hy']
  · have hy0 : 0 ≤ -y := by linarith
    have hy' : -y ≤ 1 / 4 := by linarith [neg_le_abs y, hy]
    rcases eq_or_lt_of_le h with h0 | hlt
    · rw [h0]
      simp
    · have hneg : 0 < -y := by linarith
      have ht : 2 * Real.pi * (-y) ≠ 0 := by positivity
      have h1 : 2 * Real.pi * (-y) + 1 < Real.exp (2 * Real.pi * (-y)) := Real.add_one_lt_exp ht
      have h2 : Real.exp (-(2 * Real.pi * y)) = Real.exp (2 * Real.pi * (-y)) := by ring_nf
      have hpos : 0 ≤ 2 * Real.pi * (-y) := by positivity
      have hu1 : 1 < Real.exp (-(2 * Real.pi * y)) := by
        rw [h2]; linarith [h1, hpos]
      have hlt' : 1 - Real.exp (-(2 * Real.pi * y)) < 0 := by linarith only [hu1]
      have h4 : |1 - Real.exp (-(2 * Real.pi * y))| = Real.exp (-(2 * Real.pi * y)) - 1 := by
        rw [abs_of_neg hlt']
        ring
      rw [h4, abs_of_nonpos h]
      have hu : 2 * Real.pi * (-y) ≤ Real.exp (-(2 * Real.pi * y)) - 1 := by rw [h2]; linarith
      have hmono : -y ≤ 2 * Real.pi * (-y) := by nlinarith [hy0, Real.pi_gt_three]
      linarith

/-- `1/8 ≤ exp (-2πy)` for `|y| ≤ 1/4`. -/
private lemma eighth_le_exp_neg {y : ℝ} (hy : |y| ≤ 1 / 4) :
    (1 : ℝ) / 8 ≤ Real.exp (-(2 * Real.pi * y)) := by
  have h1 : -(Real.pi / 2) ≤ -(2 * Real.pi * y) := by
    nlinarith [Real.pi_pos, le_abs_self y, hy]
  exact le_trans exp_neg_pi_div_two_ge_eighth (Real.exp_le_exp.mpr h1)

/-- `1/4 ≤ (1 - exp (-2πy))²` for `1/4 ≤ |y|`. -/
private lemma quarter_le_one_sub_exp_neg_sq {y : ℝ} (hy : 1 / 4 ≤ |y|) :
    (1 : ℝ) / 4 ≤ (1 - Real.exp (-(2 * Real.pi * y))) ^ 2 := by
  rcases le_total 0 y with h | h
  · have hy' : 1 / 4 ≤ y := by rwa [abs_of_nonneg h] at hy
    have h1 : -(2 * Real.pi * y) ≤ -(Real.pi / 2) := by nlinarith [Real.pi_pos, hy']
    have h2 : Real.exp (-(2 * Real.pi * y)) ≤ Real.exp (-(Real.pi / 2)) :=
      Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-(2 * Real.pi * y)) ≤ 1 / 2 := le_trans h2 exp_neg_pi_div_two_le_half
    have h4 : (0 : ℝ) < Real.exp (-(2 * Real.pi * y)) := Real.exp_pos _
    nlinarith [h3, h4]
  · have hy' : 1 / 4 ≤ -y := by rwa [abs_of_nonpos h] at hy
    have h1 : Real.pi / 2 ≤ -(2 * Real.pi * y) := by nlinarith [Real.pi_pos, hy']
    have h2 : Real.exp (Real.pi / 2) ≤ Real.exp (-(2 * Real.pi * y)) :=
      Real.exp_le_exp.mpr h1
    have h3 : (2 : ℝ) ≤ Real.exp (-(2 * Real.pi * y)) :=
      le_trans two_le_exp_pi_div_two h2
    nlinarith [h3]

private lemma exp_key (x y : ℝ) :
    1 - 2 * (Real.exp (-(2 * Real.pi * y)) * Real.cos (2 * Real.pi * x))
        + Real.exp (-(2 * Real.pi * y)) ^ 2
      = (1 - Real.exp (-(2 * Real.pi * y))) ^ 2
        + 2 * Real.exp (-(2 * Real.pi * y)) * (1 - Real.cos (2 * Real.pi * x)) := by ring

/-- Real core of the "near" case of A.1.7(ii). -/
private lemma near_core {x y : ℝ} (hxy : x ^ 2 + y ^ 2 ≤ 1 / 4) (hx : |x| ≤ 1 / 2) :
    x ^ 2 + y ^ 2 ≤ 1 - 2 * (Real.exp (-(2 * Real.pi * y)) * Real.cos (2 * Real.pi * x))
      + Real.exp (-(2 * Real.pi * y)) ^ 2 := by
  have hu0 : 0 < Real.exp (-(2 * Real.pi * y)) := Real.exp_pos _
  rw [exp_key]
  rcases le_total |y| (1 / 4) with hy | hy
  · have hA : y ^ 2 ≤ (1 - Real.exp (-(2 * Real.pi * y))) ^ 2 := by
      have h1 := abs_y_le_one_sub_exp_neg hy
      rw [← sq_abs y, ← sq_abs (1 - Real.exp (-(2 * Real.pi * y)))]
      exact pow_le_pow_left₀ (abs_nonneg y) h1 2
    have hB : x ^ 2 ≤ 2 * Real.exp (-(2 * Real.pi * y)) * (1 - Real.cos (2 * Real.pi * x)) := by
      have h1 := eighth_le_exp_neg hy
      have h2 := one_sub_cos_two_pi_ge hx
      nlinarith [h1, h2]
    linarith
  · have hA : (1 : ℝ) / 4 ≤ (1 - Real.exp (-(2 * Real.pi * y))) ^ 2 :=
      quarter_le_one_sub_exp_neg_sq hy
    have hB : (0 : ℝ) ≤ 2 * Real.exp (-(2 * Real.pi * y)) * (1 - Real.cos (2 * Real.pi * x)) := by
      have h3 : 0 ≤ 1 - Real.cos (2 * Real.pi * x) := by
        have := Real.cos_le_one (2 * Real.pi * x); linarith
      positivity
    linarith

/-- Real core of the "far" case of A.1.7(ii). -/
private lemma far_core {x y : ℝ} (hxy : 1 / 4 ≤ x ^ 2 + y ^ 2) (hx : |x| ≤ 1 / 2) :
    (1 : ℝ) / 4 ≤ 1 - 2 * (Real.exp (-(2 * Real.pi * y)) * Real.cos (2 * Real.pi * x))
      + Real.exp (-(2 * Real.pi * y)) ^ 2 := by
  have hu0 : 0 < Real.exp (-(2 * Real.pi * y)) := Real.exp_pos _
  rw [exp_key]
  rcases le_total |y| (1 / 4) with hy | hy
  · have h1 := eighth_le_exp_neg hy
    have h2 := one_sub_cos_two_pi_ge hx
    have h3 : 3 / 2 ≤ 8 * x ^ 2 := by
      have h4 : y ^ 2 ≤ 1 / 16 := by
        rw [← sq_abs y]; nlinarith [hy, abs_nonneg y]
      nlinarith [hxy, h4]
    nlinarith [h1, h2, h3, hu0]
  · have hA : (1 : ℝ) / 4 ≤ (1 - Real.exp (-(2 * Real.pi * y))) ^ 2 :=
      quarter_le_one_sub_exp_neg_sq hy
    have hB : (0 : ℝ) ≤ 2 * Real.exp (-(2 * Real.pi * y)) * (1 - Real.cos (2 * Real.pi * x)) := by
      have h3 : 0 ≤ 1 - Real.cos (2 * Real.pi * x) := by
        have := Real.cos_le_one (2 * Real.pi * x); linarith
      positivity
    linarith

private theorem gate_exp_near (δ : ℂ) (h1 : ‖δ‖ ≤ 1 / 2) (h2 : |δ.re| ≤ 1 / 2) :
    ‖δ‖ ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * δ)‖ := by
  have hnorm : ‖δ‖ ^ 2 = δ.re ^ 2 + δ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hxy : δ.re ^ 2 + δ.im ^ 2 ≤ 1 / 4 := by
    nlinarith [norm_nonneg δ, h1, hnorm]
  have hmain := near_core hxy h2
  have h2' : ‖δ‖ ^ 2 ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * δ)‖ ^ 2 := by
    rw [hnorm, exp_two_pi_I_sq]; exact hmain
  have := sq_le_sq.mp h2'
  rwa [abs_of_nonneg (norm_nonneg δ),
    abs_of_nonneg (norm_nonneg (1 - Complex.exp (2 * Real.pi * Complex.I * δ)))] at this

private theorem gate_exp_far (δ : ℂ) (h1 : 1 / 2 ≤ ‖δ‖) (h2 : |δ.re| ≤ 1 / 2) :
    1 / 2 ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * δ)‖ := by
  have hnorm : ‖δ‖ ^ 2 = δ.re ^ 2 + δ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hxy : 1 / 4 ≤ δ.re ^ 2 + δ.im ^ 2 := by
    nlinarith [norm_nonneg δ, h1, hnorm]
  have hmain := far_core hxy h2
  have h2' : ((1 / 2 : ℝ) ^ 2) ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * δ)‖ ^ 2 := by
    rw [exp_two_pi_I_sq]; norm_num; exact hmain
  have h3 := sq_le_sq.mp h2'
  rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    abs_of_nonneg (norm_nonneg (1 - Complex.exp (2 * Real.pi * Complex.I * δ)))] at h3

private lemma half_le_norm_of_re_add_abs_im {ζ : ℂ} {ξ : ℝ} (h : ξ ≤ ζ.re + |ζ.im|) :
    ξ / 2 ≤ ‖ζ‖ := by
  have h1 : |ζ.re| ≤ ‖ζ‖ := Complex.abs_re_le_norm ζ
  have h2 : |ζ.im| ≤ ‖ζ‖ := Complex.abs_im_le_norm ζ
  have h3 : ζ.re ≤ |ζ.re| := le_abs_self ζ.re
  linarith

private lemma half_le_norm_of_abs_re_add_abs_im {ζ : ℂ} {ξ : ℝ} (h : ξ < |ζ.re| + |ζ.im|) :
    ξ / 2 ≤ ‖ζ‖ := by
  have h1 : |ζ.re| ≤ ‖ζ‖ := Complex.abs_re_le_norm ζ
  have h2 : |ζ.im| ≤ ‖ζ‖ := Complex.abs_im_le_norm ζ
  linarith

private lemma one_div_re_pos {α : ℂ} (hα : MandelDim.InF1 α) : 0 < (1 / α).re := by
  simp only [MandelDim.InF1] at hα
  have hre : 0 < α.re := by have := abs_nonneg α.im; linarith
  have hne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr hne
  rw [Complex.div_re]
  simp only [Complex.one_re, Complex.one_im, zero_mul, zero_div, one_mul, add_zero]
  exact div_pos hre hns

private lemma one_div_im_abs_lt {α : ℂ} (hα : MandelDim.InF1 α) :
    |(1 / α).im| < (1 / α).re := by
  simp only [MandelDim.InF1] at hα
  have hre : 0 < α.re := by have := abs_nonneg α.im; linarith
  have hne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr hne
  rw [Complex.div_re, Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, zero_mul, zero_div, one_mul, add_zero, sub_zero,
    zero_sub]
  rw [abs_neg, abs_div, abs_of_pos hns, div_lt_div_iff_of_pos_right hns]
  exact hα

private theorem gate_lattice_plus {α : ℂ} {ξ : ℝ} {w : ℂ} (hξ : 0 < ξ) (hα : MandelDim.InF1 α)
    (hw : w ∈ MandelDim.Qreg (some (ξ : ℂ)) (some (-(ξ : ℂ) + 1 / α))) (k : ℤ) :
    ξ / 2 ≤ ‖w - (k : ℂ) / α‖ := by
  set A : ℂ := 1 / α with hA
  have hp : 0 < A.re := by rw [hA]; exact one_div_re_pos hα
  have hq : |A.im| ≤ A.re := le_of_lt (by rw [hA]; exact one_div_im_abs_lt hα)
  have hdiv : (k : ℂ) / α = (k : ℂ) * A := by rw [hA, one_div, div_eq_mul_inv]
  rw [hdiv]
  -- the two region conditions, in coordinates
  have h1 : -|w.im| < w.re - ξ := by
    have h := hw.1 (ξ : ℂ) (by simp)
    have e : (w - (ξ : ℂ)).im = w.im := by simp
    have e' : (w - (ξ : ℂ)).re = w.re - ξ := by simp
    rwa [e, e'] at h
  have h2 : w.re + ξ - A.re < |w.im - A.im| := by
    have h := hw.2 (-(ξ : ℂ) + A) (by simp [hA])
    have e : (w - (-(ξ : ℂ) + A)).re = w.re + ξ - A.re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]; ring
    have e' : (w - (-(ξ : ℂ) + A)).im = w.im - A.im := by
      simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im]; ring
    rwa [e, e'] at h
  have hre : ∀ j : ℤ, (w - (j : ℂ) * A).re = w.re - (j : ℝ) * A.re := by
    intro j; rw [Complex.sub_re, Complex.mul_re]; simp
  have him : ∀ j : ℤ, (w - (j : ℂ) * A).im = w.im - (j : ℝ) * A.im := by
    intro j; rw [Complex.sub_im, Complex.mul_im]; simp
  -- k ≤ 0 : use the condition at b₁ = ξ
  have keyA : ∀ j : ℤ, j ≤ 0 → ξ ≤ (w - (j : ℂ) * A).re + |(w - (j : ℂ) * A).im| := by
    intro j hj
    have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    have hjabs : |(j : ℝ)| = -(j : ℝ) := abs_of_nonpos hj'
    have hm : (0 : ℝ) ≤ -(j : ℝ) := by linarith
    have hwe : w.im = (w - (j : ℂ) * A).im + (j : ℝ) * A.im := by rw [him j]; ring
    have hle : |w.im| ≤ |(w - (j : ℂ) * A).im| + (-(j : ℝ)) * A.re := by
      rw [hwe]
      have h3 : |(j : ℝ) * A.im| ≤ (-(j : ℝ)) * A.re := by
        rw [abs_mul, hjabs]
        exact mul_le_mul_of_nonneg_left hq hm
      calc |(w - (j : ℂ) * A).im + (j : ℝ) * A.im|
          ≤ |(w - (j : ℂ) * A).im| + |(j : ℝ) * A.im| := abs_add_le _ _
        _ ≤ |(w - (j : ℂ) * A).im| + (-(j : ℝ)) * A.re := by linarith
    have hwr : w.re = (w - (j : ℂ) * A).re + (j : ℝ) * A.re := by rw [hre j]; ring
    calc ξ ≤ w.re + |w.im| := le_of_lt (by linarith [h1])
      _ = (w - (j : ℂ) * A).re + (j : ℝ) * A.re + |w.im| := by rw [hwr]
      _ ≤ (w - (j : ℂ) * A).re + (j : ℝ) * A.re
            + (|(w - (j : ℂ) * A).im| + (-(j : ℝ)) * A.re) := by linarith [hle]
      _ = (w - (j : ℂ) * A).re + |(w - (j : ℂ) * A).im| := by ring
  -- k ≥ 1 : use the condition at b₂ = -ξ + 1/α
  have keyB : ∀ j : ℤ, 1 ≤ j → (w - (j : ℂ) * A).re + ξ < |(w - (j : ℂ) * A).im| := by
    intro j hj
    have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hcoef : (0 : ℝ) ≤ (j : ℝ) - 1 := by linarith
    have hwe : w.im - A.im = (w - (j : ℂ) * A).im + ((j : ℝ) - 1) * A.im := by rw [him j]; ring
    have hle : |w.im - A.im| ≤ |(w - (j : ℂ) * A).im| + ((j : ℝ) - 1) * A.re := by
      rw [hwe]
      have h3 : |((j : ℝ) - 1) * A.im| ≤ ((j : ℝ) - 1) * A.re := by
        rw [abs_mul, abs_of_nonneg hcoef]
        exact mul_le_mul_of_nonneg_left hq hcoef
      calc |(w - (j : ℂ) * A).im + ((j : ℝ) - 1) * A.im|
          ≤ |(w - (j : ℂ) * A).im| + |((j : ℝ) - 1) * A.im| := abs_add_le _ _
        _ ≤ |(w - (j : ℂ) * A).im| + ((j : ℝ) - 1) * A.re := by linarith
    have hwr : w.re + ξ - A.re
        = (w - (j : ℂ) * A).re + ξ + ((j : ℝ) - 1) * A.re := by rw [hre j]; ring
    have h3 : (w - (j : ℂ) * A).re + ξ + ((j : ℝ) - 1) * A.re < |w.im - A.im| := by
      rw [← hwr]; exact h2
    linarith [h3, hle]
  rcases le_total k 0 with hk | hk
  · exact half_le_norm_of_re_add_abs_im (keyA k hk)
  · rcases eq_or_lt_of_le hk with h0 | hpos
    · exact half_le_norm_of_re_add_abs_im (keyA k (le_of_eq h0.symm))
    · have hk1 : (1 : ℤ) ≤ k := hpos
      have hsrc : (w - (k : ℂ) * A).re + ξ < |(w - (k : ℂ) * A).im| := keyB k hk1
      have h4 : ξ < |(w - (k : ℂ) * A).re| + |(w - (k : ℂ) * A).im| := by
        rcases le_total 0 (w - (k : ℂ) * A).re with hr | hr
        · rw [abs_of_nonneg hr]; linarith [hsrc, abs_nonneg (w - (k : ℂ) * A).im]
        · rw [abs_of_nonpos hr]; linarith [hsrc]
      exact half_le_norm_of_abs_re_add_abs_im h4

private theorem gate_lattice_minus {α : ℂ} {ξ : ℝ} {w : ℂ} (hξ : 0 < ξ) (hα : MandelDim.InF1 α)
    (hw : w ∈ MandelDim.Qreg (some ((ξ : ℂ) - 1 / α)) (some (-(ξ : ℂ)))) (k : ℤ) :
    ξ / 2 ≤ ‖w - (k : ℂ) / α‖ := by
  set A : ℂ := 1 / α with hA
  have hp : 0 < A.re := by rw [hA]; exact one_div_re_pos hα
  have hq : |A.im| ≤ A.re := le_of_lt (by rw [hA]; exact one_div_im_abs_lt hα)
  have hdiv : (k : ℂ) / α = (k : ℂ) * A := by rw [hA, one_div, div_eq_mul_inv]
  rw [hdiv]
  have h1 : w.re - ξ + A.re > -|w.im + A.im| := by
    have h := hw.1 ((ξ : ℂ) - A) (by simp [hA])
    have e : (w - ((ξ : ℂ) - A)).re = w.re - ξ + A.re := by
      simp only [Complex.sub_re, Complex.ofReal_re]; ring
    have e' : (w - ((ξ : ℂ) - A)).im = w.im + A.im := by
      simp only [Complex.sub_im, Complex.ofReal_im]; ring
    rwa [e, e'] at h
  have h2 : w.re + ξ < |w.im| := by
    have h := hw.2 (-(ξ : ℂ)) (by simp)
    have e : (w - (-(ξ : ℂ))).re = w.re + ξ := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]; ring
    have e' : (w - (-(ξ : ℂ))).im = w.im := by
      simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im]; ring
    rwa [e, e'] at h
  have hre : ∀ j : ℤ, (w - (j : ℂ) * A).re = w.re - (j : ℝ) * A.re := by
    intro j; rw [Complex.sub_re, Complex.mul_re]; simp
  have him : ∀ j : ℤ, (w - (j : ℂ) * A).im = w.im - (j : ℝ) * A.im := by
    intro j; rw [Complex.sub_im, Complex.mul_im]; simp
  -- 0 ≤ k : use the condition at b₂ = -ξ
  have keyA : ∀ j : ℤ, 0 ≤ j → (w - (j : ℂ) * A).re + ξ < |(w - (j : ℂ) * A).im| := by
    intro j hj
    have hj' : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hwe : w.im = (w - (j : ℂ) * A).im + (j : ℝ) * A.im := by rw [him j]; ring
    have hle : |w.im| ≤ |(w - (j : ℂ) * A).im| + (j : ℝ) * A.re := by
      rw [hwe]
      have h3 : |(j : ℝ) * A.im| ≤ (j : ℝ) * A.re := by
        rw [abs_mul, abs_of_nonneg hj']
        exact mul_le_mul_of_nonneg_left hq hj'
      calc |(w - (j : ℂ) * A).im + (j : ℝ) * A.im|
          ≤ |(w - (j : ℂ) * A).im| + |(j : ℝ) * A.im| := abs_add_le _ _
        _ ≤ |(w - (j : ℂ) * A).im| + (j : ℝ) * A.re := by linarith
    have hwr : w.re + ξ = (w - (j : ℂ) * A).re + ξ + (j : ℝ) * A.re := by rw [hre j]; ring
    have h3 : (w - (j : ℂ) * A).re + ξ + (j : ℝ) * A.re < |w.im| := by
      rw [← hwr]; exact h2
    linarith [h3, hle]
  -- k ≤ -1 : use the condition at b₁ = ξ - 1/α
  have keyB : ∀ j : ℤ, j ≤ -1 → ξ ≤ (w - (j : ℂ) * A).re + |(w - (j : ℂ) * A).im| := by
    intro j hj
    have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast hj
    set m : ℝ := -((j : ℝ) + 1) with hm_def
    have hm : 0 ≤ m := by rw [hm_def]; linarith
    have hwe : w.im + A.im = (w - (j : ℂ) * A).im - m * A.im := by rw [him j, hm_def]; ring
    have hle : |w.im + A.im| ≤ |(w - (j : ℂ) * A).im| + m * A.re := by
      rw [hwe]
      have h3 : |m * A.im| ≤ m * A.re := by
        rw [abs_mul, abs_of_nonneg hm]
        exact mul_le_mul_of_nonneg_left hq hm
      calc |(w - (j : ℂ) * A).im - m * A.im|
          = |(w - (j : ℂ) * A).im + -(m * A.im)| := by ring_nf
        _ ≤ |(w - (j : ℂ) * A).im| + |-(m * A.im)| := abs_add_le _ _
        _ = |(w - (j : ℂ) * A).im| + |m * A.im| := by rw [abs_neg]
        _ ≤ |(w - (j : ℂ) * A).im| + m * A.re := by linarith
    have hwr : w.re - ξ + A.re = (w - (j : ℂ) * A).re - m * A.re - ξ := by
      rw [hre j, hm_def]; ring
    have h3 : -|w.im + A.im| < (w - (j : ℂ) * A).re - m * A.re - ξ := by
      rw [← hwr]; exact h1
    linarith [h3, hle]
  rcases lt_or_ge k 0 with hk | hk
  · have hk1 : k ≤ -1 := by omega
    exact half_le_norm_of_re_add_abs_im (keyB k hk1)
  · have hsrc : (w - (k : ℂ) * A).re + ξ < |(w - (k : ℂ) * A).im| := keyA k hk
    have h4 : ξ < |(w - (k : ℂ) * A).re| + |(w - (k : ℂ) * A).im| := by
      rcases le_total 0 (w - (k : ℂ) * A).re with hr | hr
      · rw [abs_of_nonneg hr]; linarith [hsrc, abs_nonneg (w - (k : ℂ) * A).im]
      · rw [abs_of_nonpos hr]; linarith [hsrc]
    exact half_le_norm_of_abs_re_add_abs_im h4



private lemma zero_mem_ball {ρ : ℝ} (hρ : 0 < ρ) : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
  simpa [Metric.mem_ball] using hρ

/-- Rounding: there is an integer within `1/2` of any real. -/
private lemma exists_int_abs_sub_le_half (x : ℝ) : ∃ k : ℤ, |x - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- `‖2πiα‖ = 2π‖α‖`. -/
private lemma norm_two_pi_I_mul (α : ℂ) : ‖2 * Real.pi * I * α‖ = 2 * Real.pi * ‖α‖ := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- `‖σ‖ ≤ 8π‖α‖` from the normalisation `1 - σ u 0 = exp(2πiα)`. -/
private lemma sigma_le {u : ℂ → ℂ} {σ α : ℂ} {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hub : ∀ z ∈ Metric.ball 0 ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * I * α))
    (hαs : ‖α‖ ≤ (10 : ℝ) ^ (-6 : ℤ)) :
    ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := by
  have hαs' : ‖α‖ ≤ 1 / 1000000 := by
    rwa [show (10 : ℝ) ^ (-6 : ℤ) = 1 / 1000000 by norm_num [zpow_neg]] at hαs
  have hρ0 : (0 : ℝ) < ρ := by linarith [hρ]
  have hu0 : 1 / 2 ≤ ‖u 0‖ := (hub 0 (zero_mem_ball hρ0)).1
  have hσu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * I * α) := by linear_combination -hnorm
  have h1 : ‖σ‖ * ‖u 0‖ = ‖1 - Complex.exp (2 * Real.pi * I * α)‖ := by
    rw [← norm_mul, hσu]
  have h2 : ‖1 - Complex.exp (2 * Real.pi * I * α)‖
      = ‖Complex.exp (2 * Real.pi * I * α) - 1‖ := by
    rw [← norm_neg]; congr 1; ring
  have h3 : ‖2 * Real.pi * I * α‖ ≤ 1 := by
    rw [norm_two_pi_I_mul α]
    have hp : Real.pi * ‖α‖ ≤ 4 * (1 / 1000000 : ℝ) :=
      mul_le_mul (le_of_lt Real.pi_lt_four) hαs' (norm_nonneg α) (by norm_num)
    nlinarith
  have h4 : ‖Complex.exp (2 * Real.pi * I * α) - 1‖ ≤ 2 * ‖2 * Real.pi * I * α‖ :=
    Complex.norm_exp_sub_one_le h3
  have hbound : ‖σ‖ * ‖u 0‖ ≤ 4 * Real.pi * ‖α‖ := by
    rw [h1, h2]
    calc ‖Complex.exp (2 * Real.pi * I * α) - 1‖ ≤ 2 * ‖2 * Real.pi * I * α‖ := h4
      _ = 2 * (2 * Real.pi * ‖α‖) := by rw [norm_two_pi_I_mul α]
      _ = 4 * Real.pi * ‖α‖ := by ring
  have hhalf : ‖σ‖ * (1 / 2) ≤ ‖σ‖ * ‖u 0‖ :=
    mul_le_mul_of_nonneg_left hu0 (norm_nonneg σ)
  nlinarith [hbound, hhalf, norm_nonneg σ, norm_nonneg α]

/-- `exp (2πiα) ≠ 1` for the small `α ≠ 0` of the gate (else `α` would be a nonzero integer). -/
private lemma exp_two_pi_I_ne_one {α : ℂ} (hαne : α ≠ 0)
    (hαs : ‖α‖ ≤ (10 : ℝ) ^ (-6 : ℤ)) : Complex.exp (2 * Real.pi * I * α) ≠ 1 := by
  have hαs' : ‖α‖ ≤ 1 / 1000000 := by
    rwa [show (10 : ℝ) ^ (-6 : ℤ) = 1 / 1000000 by norm_num [zpow_neg]] at hαs
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h2 : α = (n : ℂ) := by
    have hfac : (2 * Real.pi * I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    refine mul_left_cancel₀ hfac ?_
    rw [hn]; ring
  rcases eq_or_ne n 0 with h0 | h0
  · rw [h0] at h2; simp at h2; exact hαne h2
  · have hge : (1 : ℝ) ≤ ‖α‖ := by
      rw [h2, Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs h0
    linarith

/-- Shishikura (A.1.7)(ii) at one point: `F_f = liftF u σ α` is a near-translation on any point
whose distance to the lattice `ℤ/α` is at least `5·10^5`. -/
private theorem gate_point {u : ℂ → ℂ} {σ α : ℂ} {ρ : ℝ} {w : ℂ}
    (hρ : 1 ≤ ρ) (hu : DifferentiableOn ℂ u (Metric.ball 0 ρ))
    (hub : ∀ z ∈ Metric.ball 0 ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * I * α))
    (hσs : ‖σ‖ ≤ (10 : ℝ) ^ (-6 : ℤ)) (hαs : ‖α‖ ≤ (10 : ℝ) ^ (-6 : ℤ))
    (hαne : α ≠ 0) (hinf : MandelDim.InF1 α)
    (hlat : ∀ k : ℤ, (10 : ℝ) ^ 6 / 2 ≤ ‖w - (k : ℂ) / α‖) :
    DifferentiableAt ℂ (liftF u σ α) w ∧ ‖liftF u σ α w - (w + 1)‖ ≤ 1 / 32 ∧
      ‖deriv (liftF u σ α) w - 1‖ ≤ 1 / 32 := by
  have hαs' : ‖α‖ ≤ 1 / 1000000 := by
    rwa [show (10 : ℝ) ^ (-6 : ℤ) = 1 / 1000000 by norm_num [zpow_neg]] at hαs
  have hσs' : ‖σ‖ ≤ 1 / 1000000 := by
    rwa [show (10 : ℝ) ^ (-6 : ℤ) = 1 / 1000000 by norm_num [zpow_neg]] at hσs
  have hlat' : ∀ k : ℤ, 500000 ≤ ‖w - (k : ℂ) / α‖ := by
    intro k
    have := hlat k
    rwa [show (10 : ℝ) ^ 6 / 2 = 500000 by norm_num] at this
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hαre : 0 < α.re := by
    have h := hinf; simp only [MandelDim.InF1] at h
    have := abs_nonneg α.im; linarith
  have hσ8 : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := sigma_le hρ hub hnorm hαs
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := zero_mem_ball (by linarith [hρ])
  have hu0b : 1 / 2 ≤ ‖u 0‖ ∧ ‖u 0‖ ≤ 2 := hub 0 h0mem
  have hA1 : Complex.exp (2 * Real.pi * I * α) ≠ 1 := exp_two_pi_I_ne_one hαne hαs
  have hσne : σ ≠ 0 := by
    intro h0
    exact hA1 (by rw [← hnorm, h0]; ring)
  -- ## the point `τ = τ_f w` and the distance to the lattice
  set τ : ℂ := σ / (1 - Complex.exp (-(2 * Real.pi * I * α * w))) with hτ
  have hτc : tauC σ α w = τ := by rw [tauC, hτ]
  set v : ℂ := -(α * w) with hv
  obtain ⟨k₀, hk₀⟩ := exists_int_abs_sub_le_half v.re
  set δ : ℂ := v - (k₀ : ℂ) with hδ
  have hδre : |δ.re| ≤ 1 / 2 := by
    have he : δ.re = v.re - (k₀ : ℝ) := by rw [hδ, Complex.sub_re]; simp
    rw [he]; exact hk₀
  have hδge : ‖α‖ * 500000 ≤ ‖δ‖ := by
    have h := hlat' (-k₀)
    have hw : w - ((-k₀ : ℤ) : ℂ) / α = w + (k₀ : ℂ) / α := by
      rw [show ((-k₀ : ℤ) : ℂ) = -(k₀ : ℂ) by simp, neg_div, sub_neg_eq_add]
    rw [hw] at h
    have hkey : δ = -(α * (w + (k₀ : ℂ) / α)) := by
      rw [hδ, hv]; field_simp; ring
    rw [hkey, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg α)
  have hexp_eq : Complex.exp (-(2 * Real.pi * I * α * w)) = Complex.exp (2 * Real.pi * I * δ) := by
    have h1 : -(2 * Real.pi * I * α * w) = 2 * Real.pi * I * v := by rw [hv]; ring
    rw [h1]
    have hvk : v = δ + (k₀ : ℂ) := by rw [hδ]; ring
    rw [hvk, show 2 * Real.pi * I * (δ + (k₀ : ℂ))
        = 2 * Real.pi * I * δ + (k₀ : ℂ) * (2 * Real.pi * I) by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hzeta : (1 : ℝ) / 2 ≤ ‖1 - Complex.exp (-(2 * Real.pi * I * α * w))‖ ∨
      ‖α‖ * 500000 ≤ ‖1 - Complex.exp (-(2 * Real.pi * I * α * w))‖ := by
    rw [hexp_eq]
    rcases le_total ‖δ‖ (1 / 2) with h | h
    · exact Or.inr (le_trans hδge (gate_exp_near δ h hδre))
    · exact Or.inl (gate_exp_far δ h hδre)
  have hζne : 1 - Complex.exp (-(2 * Real.pi * I * α * w)) ≠ 0 := by
    intro h0
    rcases hzeta with h | h
    · rw [h0, norm_zero] at h; norm_num at h
    · rw [h0, norm_zero] at h
      have := mul_pos hαpos (by norm_num : (0 : ℝ) < 500000)
      linarith
  have hτb : ‖τ‖ ≤ 51 / 1000000 := by
    rw [hτ, norm_div]
    rcases hzeta with h | h
    · calc ‖σ‖ / ‖1 - Complex.exp (-(2 * Real.pi * I * α * w))‖ ≤ ‖σ‖ / (1 / 2) :=
            div_le_div_of_nonneg_left (norm_nonneg σ) (by norm_num) h
        _ ≤ (8 * Real.pi * ‖α‖) / (1 / 2) := div_le_div_of_nonneg_right hσ8 (by norm_num)
        _ = 16 * Real.pi * ‖α‖ := by ring
        _ ≤ 51 / 1000000 := by
            have hp : Real.pi * ‖α‖ ≤ 3.1416 * (1 / 1000000 : ℝ) :=
              mul_le_mul (le_of_lt Real.pi_lt_d4) hαs' (norm_nonneg α) (by norm_num)
            nlinarith
    · have hden : (0 : ℝ) < ‖α‖ * 500000 := mul_pos hαpos (by norm_num)
      calc ‖σ‖ / ‖1 - Complex.exp (-(2 * Real.pi * I * α * w))‖
          ≤ ‖σ‖ / (‖α‖ * 500000) := div_le_div_of_nonneg_left (norm_nonneg σ) hden h
        _ ≤ (8 * Real.pi * ‖α‖) / (‖α‖ * 500000) :=
            div_le_div_of_nonneg_right hσ8 (le_of_lt hden)
        _ = 16 * Real.pi / 1000000 := by field_simp; ring
        _ ≤ 51 / 1000000 := by
            rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 1000000)]
            nlinarith [Real.pi_lt_d4]
  have hτρ : τ ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hτb, hρ]
  have huτ : DifferentiableAt ℂ u τ := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hτρ)
  have huτb : 1 / 2 ≤ ‖u τ‖ ∧ ‖u τ‖ ≤ 2 := hub τ hτρ
  -- ## Cauchy estimates and the mean value bound
  have hderiv_le : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖deriv u z‖ ≤ 8 := by
    intro z hz
    have hsub : Metric.ball z (1 / 4) ⊆ Metric.ball (0 : ℂ) ρ := by
      intro y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖y‖ = ‖(y - z) + z‖ := by ring_nf
        _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
        _ < 1 / 4 + 1 / 2 := by linarith
        _ < ρ := by linarith
    have hclo : closure (Metric.ball z (1 / 4)) ⊆ Metric.ball (0 : ℂ) ρ := by
      rw [closure_ball z (by norm_num : (1 / 4 : ℝ) ≠ 0)]
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖y‖ = ‖(y - z) + z‖ := by ring_nf
        _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 / 2 := by linarith
        _ < ρ := by linarith
    have hdiff : DiffContOnCl ℂ u (Metric.ball z (1 / 4)) :=
      ⟨hu.mono hsub, (hu.mono hclo).continuousOn⟩
    have hbd : ∀ y ∈ Metric.sphere z (1 / 4), ‖u y‖ ≤ 2 := by
      intro y hy
      rw [Metric.mem_sphere, dist_eq_norm] at hy
      refine (hub y ?_).2
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖y‖ = ‖(y - z) + z‖ := by ring_nf
        _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
        _ = 1 / 4 + ‖z‖ := by rw [hy]
        _ ≤ 1 / 4 + 1 / 2 := by linarith
        _ < ρ := by linarith
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := u) (c := z) (R := 1 / 4)
      (C := 2) (by norm_num) hdiff hbd
    have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8] at h
    exact h
  have hmvt : ‖u 0 - u τ‖ ≤ 8 * ‖τ‖ := by
    have hbd : ∀ x ∈ Metric.closedBall (0 : ℂ) (1 / 2), ‖deriv u x‖ ≤ 8 := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hderiv_le x hx
    have hdiff : ∀ x ∈ Metric.closedBall (0 : ℂ) (1 / 2), DifferentiableAt ℂ u x := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      refine hu.differentiableAt (Metric.isOpen_ball.mem_nhds ?_)
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hτc2 : τ ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith [hτb]
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := u)
      (s := Metric.closedBall (0 : ℂ) (1 / 2)) (x := (0 : ℂ)) (y := τ) (C := 8)
      hdiff hbd (convex_closedBall 0 (1 / 2)) (by simp [Metric.mem_closedBall]) hτc2
    rwa [sub_zero, norm_sub_rev] at h
  -- ## the quantities `s = sfun u σ α w` and `E`
  have h1pu : 1 + τ * u τ ≠ 0 := by
    have h1 : ‖τ * u τ‖ ≤ 2 * ‖τ‖ := by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right huτb.2 (norm_nonneg τ)
    have h2 : (1 : ℝ) / 2 ≤ ‖1 + τ * u τ‖ := by
      have h4 : ‖(1 : ℂ) + τ * u τ‖ = ‖1 - (-(τ * u τ))‖ := by ring_nf
      rw [h4]
      have h5 : 1 - ‖τ * u τ‖ ≤ ‖1 - (-(τ * u τ))‖ := by
        have := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
        rw [norm_one, norm_neg] at this
        linarith [le_abs_self (1 - ‖τ * u τ‖)]
      linarith [h1, hτb, h5]
    intro h
    rw [h, norm_zero] at h2
    norm_num at h2
  have hks : 1 + τ * u τ - σ * u τ ≠ 0 := by
    have h1 : ‖τ * u τ‖ ≤ 2 * ‖τ‖ := by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right huτb.2 (norm_nonneg τ)
    have h2 : ‖σ * u τ‖ ≤ (8 * Real.pi * ‖α‖) * 2 := by
      rw [norm_mul]
      exact mul_le_mul hσ8 huτb.2 (norm_nonneg (u τ)) (by positivity)
    have h3 : 1 - ‖τ‖ * 2 ≤ ‖1 + τ * u τ‖ := by
      have h4 : ‖(1 : ℂ) + τ * u τ‖ = ‖1 - (-(τ * u τ))‖ := by ring_nf
      rw [h4]
      have h5 : 1 - ‖τ * u τ‖ ≤ ‖1 - (-(τ * u τ))‖ := by
        have := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
        rw [norm_one, norm_neg] at this
        linarith [le_abs_self (1 - ‖τ * u τ‖)]
      linarith [h1, h5]
    have h4 : ‖1 + τ * u τ‖ - ‖σ * u τ‖ ≤ ‖1 + τ * u τ - σ * u τ‖ := by
      have := abs_norm_sub_norm_le (1 + τ * u τ) (σ * u τ)
      linarith [le_abs_self (‖1 + τ * u τ‖ - ‖σ * u τ‖)]
    have h5 : (8 * Real.pi * ‖α‖) * 2 ≤ 1 / 8 := by
      have hp : Real.pi * ‖α‖ ≤ 3.1416 * (1 / 1000000 : ℝ) :=
        mul_le_mul (le_of_lt Real.pi_lt_d4) hαs' (norm_nonneg α) (by norm_num)
      nlinarith
    have h6 : ‖τ‖ * 2 ≤ 1 / 8 := by
      have : (51 : ℝ) / 1000000 ≤ 1 / 16 := by norm_num
      linarith [hτb]
    have h7 : (1 : ℝ) / 4 ≤ ‖1 + τ * u τ - σ * u τ‖ := by linarith [h2, h3, h4, h5, h6]
    intro h
    rw [h, norm_zero] at h7
    norm_num at h7
  -- ## the normalisation `A`, the error `E`, and `1 - s = A(1+E)`
  set A : ℂ := Complex.exp (2 * Real.pi * I * α) with hA
  have hAe : (1 : ℂ) - σ * u 0 = A := by rw [hA]; exact hnorm
  have hAsmall : ‖A - 1‖ ≤ 1 / 2 := by
    have h1 : ‖A - 1‖ = ‖1 - A‖ := norm_sub_rev _ _
    rw [h1, ← hAe]
    have h2 : (1 : ℂ) - (1 - σ * u 0) = σ * u 0 := by ring
    rw [h2]
    calc ‖σ * u 0‖ ≤ ‖σ‖ * 2 := by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left hu0b.2 (norm_nonneg σ)
      _ ≤ (8 * Real.pi * ‖α‖) * 2 := by
          exact mul_le_mul_of_nonneg_right hσ8 (by norm_num)
      _ ≤ 1 / 2 := by
          have hp : Real.pi * ‖α‖ ≤ 3.1416 * (1 / 1000000 : ℝ) :=
            mul_le_mul (le_of_lt Real.pi_lt_d4) hαs' (norm_nonneg α) (by norm_num)
          nlinarith
  have hAre : 1 / 2 ≤ A.re := by
    have h1 : |(A - 1).re| ≤ ‖A - 1‖ := Complex.abs_re_le_norm (A - 1)
    have h2 : (A - 1).re = A.re - 1 := by simp
    rw [h2] at h1
    have h3 := neg_le_abs (A.re - 1)
    linarith
  have hAne : A ≠ 0 := by
    intro h
    rw [h] at hAre
    norm_num at hAre
  set sfunw : ℂ := σ * u τ / (1 + τ * u τ) with hsfun
  have hsfun_eq : sfun u σ α w = sfunw := by rw [sfun, hτc, hsfun]
  set E : ℂ := σ * (u 0 - u τ + u 0 * (τ * u τ)) / (A * (1 + τ * u τ)) with hEdef
  have hEid : 1 - sfunw = A * (1 + E) := by
    have hA0 : (1 : ℂ) - σ * u 0 ≠ 0 := by rw [hAe]; exact hAne
    have hcomm : (1 : ℂ) + u τ * τ ≠ 0 := by rw [mul_comm]; exact h1pu
    rw [hEdef, hsfun, ← hAe]
    field_simp [hcomm]
    ring
  have hEbound : ‖E‖ ≤ 48 * ‖σ‖ * ‖τ‖ := by
    have hnum : ‖σ * (u 0 - u τ + u 0 * (τ * u τ))‖ ≤ 12 * ‖σ‖ * ‖τ‖ := by
      rw [norm_mul]
      have h2 : ‖u 0 - u τ + u 0 * (τ * u τ)‖ ≤ 12 * ‖τ‖ := by
        have h3 : ‖u 0 * (τ * u τ)‖ ≤ 2 * (2 * ‖τ‖) := by
          rw [norm_mul]
          have h4 : ‖τ * u τ‖ ≤ 2 * ‖τ‖ := by
            rw [norm_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right huτb.2 (norm_nonneg τ)
          nlinarith [hu0b.2, norm_nonneg (τ * u τ)]
        calc ‖u 0 - u τ + u 0 * (τ * u τ)‖ ≤ ‖u 0 - u τ‖ + ‖u 0 * (τ * u τ)‖ :=
              norm_add_le _ _
          _ ≤ 8 * ‖τ‖ + 4 * ‖τ‖ := by linarith [hmvt, h3]
          _ = 12 * ‖τ‖ := by ring
      calc ‖σ‖ * ‖u 0 - u τ + u 0 * (τ * u τ)‖ ≤ ‖σ‖ * (12 * ‖τ‖) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg σ)
        _ = 12 * ‖σ‖ * ‖τ‖ := by ring
    have hden : (1 : ℝ) / 4 ≤ ‖A * (1 + τ * u τ)‖ := by
      rw [norm_mul]
      have h2 : 1 / 2 ≤ ‖A‖ := by
        have h1 : |‖A‖ - 1| ≤ ‖A - 1‖ := by
          have := abs_norm_sub_norm_le A 1
          rwa [norm_one] at this
        linarith [hAsmall, neg_le_abs (‖A‖ - 1)]
      have h3 : 1 / 2 ≤ ‖1 + τ * u τ‖ := by
        have h4 : ‖τ * u τ‖ ≤ 2 * ‖τ‖ := by
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right huτb.2 (norm_nonneg τ)
        have h5 : ‖(1 : ℂ) + τ * u τ‖ = ‖1 - (-(τ * u τ))‖ := by ring_nf
        rw [h5]
        have h6 : 1 - ‖τ * u τ‖ ≤ ‖1 - (-(τ * u τ))‖ := by
          have := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
          rw [norm_one, norm_neg] at this
          linarith [le_abs_self (1 - ‖τ * u τ‖)]
        have h7 : 2 * ‖τ‖ ≤ 1 / 2 := by linarith [hτb]
        linarith [h4, h6, h7]
      nlinarith [h2, h3]
    calc ‖E‖ = ‖σ * (u 0 - u τ + u 0 * (τ * u τ))‖ / ‖A * (1 + τ * u τ)‖ := by
          rw [hEdef, norm_div]
      _ ≤ (12 * ‖σ‖ * ‖τ‖) / ‖A * (1 + τ * u τ)‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (12 * ‖σ‖ * ‖τ‖) / (1 / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = 48 * ‖σ‖ * ‖τ‖ := by ring
  have hEhalf : ‖E‖ ≤ 1 / 2 := by
    have h1 : 48 * ‖σ‖ * ‖τ‖ ≤ 48 * (8 * Real.pi * ‖α‖) * (51 / 1000000) := by
      nlinarith [hσ8, hτb, norm_nonneg σ, norm_nonneg α, norm_nonneg τ]
    have h2 : 48 * (8 * Real.pi * ‖α‖) * (51 / 1000000) ≤ 1 / 2 := by
      have hp : Real.pi * ‖α‖ ≤ 3.1416 * (1 / 1000000 : ℝ) :=
        mul_le_mul (le_of_lt Real.pi_lt_d4) hαs' (norm_nonneg α) (by norm_num)
      nlinarith
    linarith [hEbound, h1, h2]
  have h1Ere : 0 < (1 + E).re := by
    have h1 : E.re ≥ -‖E‖ := by
      have := neg_abs_le E.re
      linarith [Complex.abs_re_le_norm E]
    have h2 : (1 + E).re = 1 + E.re := by simp
    rw [h2]; linarith
  have h1Ene : (1 : ℂ) + E ≠ 0 := by
    intro h; rw [h] at h1Ere; norm_num at h1Ere
  -- ## the logarithm
  have hlogmul : Complex.log (1 - sfun u σ α w) = Complex.log A + Complex.log (1 + E) := by
    rw [hsfun_eq, hEid]
    refine Complex.log_mul hAne h1Ene ?_
    have h1 : A.arg < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith [hAre]))
    have h2 : -(Real.pi / 2) < A.arg :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl (by linarith [hAre]))
    have h3 : (1 + E).arg < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl h1Ere)
    have h4 : -(Real.pi / 2) < (1 + E).arg :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl h1Ere)
    refine ⟨?_, ?_⟩ <;> linarith
  have hlogA : Complex.log A = 2 * Real.pi * I * α := by
    rw [hA]
    refine Complex.log_exp ?_ ?_
    · have hIm : (2 * Real.pi * I * α).im = 2 * Real.pi * α.re := by
        simp [Complex.mul_im, Complex.mul_re]
      rw [hIm]; nlinarith [Real.pi_pos, hαre]
    · have hIm : (2 * Real.pi * I * α).im = 2 * Real.pi * α.re := by
        simp [Complex.mul_im, Complex.mul_re]
      rw [hIm]
      have h1 : α.re ≤ ‖α‖ := Complex.re_le_norm α
      nlinarith [Real.pi_pos]
  have hlift_eq : liftF u σ α w = w + 1 + (1 / (2 * Real.pi * I * α)) * Complex.log (1 + E) := by
    rw [liftF, hlogmul, hlogA]
    field_simp
    ring
  have hval : ‖liftF u σ α w - (w + 1)‖ ≤ 1 / 32 := by
    have h1 : liftF u σ α w - (w + 1)
        = (1 / (2 * Real.pi * I * α)) * Complex.log (1 + E) := by
      rw [hlift_eq]; ring
    have hlogb : ‖Complex.log (1 + E)‖ ≤ 3 / 2 * ‖E‖ :=
      Complex.norm_log_one_add_half_le_self hEhalf
    have hfac : ‖((1 : ℂ) / (2 * Real.pi * I * α))‖ = 1 / (2 * Real.pi * ‖α‖) := by
      rw [norm_div, norm_one, norm_two_pi_I_mul α]
    rw [h1, norm_mul, hfac]
    have hpos : (0 : ℝ) < 1 / (2 * Real.pi * ‖α‖) := by positivity
    calc (1 / (2 * Real.pi * ‖α‖)) * ‖Complex.log (1 + E)‖
        ≤ (1 / (2 * Real.pi * ‖α‖)) * (3 / 2 * ‖E‖) :=
          mul_le_mul_of_nonneg_left hlogb (le_of_lt hpos)
      _ ≤ (1 / (2 * Real.pi * ‖α‖)) * (3 / 2 * (48 * ‖σ‖ * ‖τ‖)) :=
          mul_le_mul_of_nonneg_left (by linarith [hEbound]) (le_of_lt hpos)
      _ ≤ (1 / (2 * Real.pi * ‖α‖))
            * (3 / 2 * (48 * (8 * Real.pi * ‖α‖) * (51 / 1000000))) :=
          mul_le_mul_of_nonneg_left
            (by nlinarith [hσ8, hτb, norm_nonneg σ, norm_nonneg τ, norm_nonneg α])
            (le_of_lt hpos)
      _ ≤ 1 / 32 := by
          have hid : (1 / (2 * Real.pi * ‖α‖))
              * (3 / 2 * (48 * (8 * Real.pi * ‖α‖) * (51 / 1000000)))
              = 3 * 48 * 8 * 51 / (1000000 * 4) := by
            field_simp
            ring
          rw [hid]
          norm_num
  -- ## the derivative: Shishikura (A.1.7)(ii) via `gate_derivF`
  have hAre2 : ‖A‖ ≤ 2 := by
    have h1 : ‖A‖ ≤ ‖A - 1‖ + 1 := by
      calc ‖A‖ = ‖(A - 1) + 1‖ := by ring_nf
        _ ≤ ‖A - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖A - 1‖ + 1 := by rw [norm_one]
    linarith [hAsmall]
  have hEtiny : ‖E‖ ≤ 1 / 8 := by
    have h1 : 48 * ‖σ‖ * ‖τ‖ ≤ 48 * (8 * Real.pi * ‖α‖) * (51 / 1000000) := by
      nlinarith [hσ8, hτb, norm_nonneg σ, norm_nonneg α, norm_nonneg τ]
    have h2 : 48 * (8 * Real.pi * ‖α‖) * (51 / 1000000) ≤ 1 / 8 := by
      have hp : Real.pi * ‖α‖ ≤ 3.1416 * (1 / 1000000 : ℝ) :=
        mul_le_mul (le_of_lt Real.pi_lt_d4) hαs' (norm_nonneg α) (by norm_num)
      nlinarith
    linarith [hEbound, h1, h2]
  have hslit : 1 - sfun u σ α w ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [hsfun_eq, hEid, mul_add, mul_one, Complex.add_re]
    have h1 : -(‖A * E‖) ≤ (A * E).re := by
      have := neg_abs_le (A * E).re
      linarith [Complex.abs_re_le_norm (A * E)]
    have h2 : ‖A * E‖ ≤ 2 * (1 / 8) := by
      rw [norm_mul]
      exact mul_le_mul hAre2 hEtiny (norm_nonneg E) (by norm_num)
    linarith [h1, h2, hAre]
  have hEne : Complex.exp (-(2 * Real.pi * I * α * w)) ≠ 1 := by
    intro h
    apply hζne
    rw [h]; ring
  have huτ' : DifferentiableAt ℂ u (tauC σ α w) := by rw [hτc]; exact huτ
  have hz : tauC σ α w ≠ 0 := by
    rw [hτc, hτ]
    exact div_ne_zero hσne hζne
  have hderivF := gate_derivF hαne hσne hz huτ' hslit hEne h1pu hks
  have hderiv_bound : ‖deriv (liftF u σ α) w - 1‖ ≤ 1 / 32 := by
    rw [hderivF.deriv]
    set X : ℂ := tauC σ α w * (tauC σ α w - σ)
      * (deriv u (tauC σ α w) - u (tauC σ α w) ^ 2) with hXdef
    set D : ℂ := (1 + tauC σ α w * u (tauC σ α w) - σ * u (tauC σ α w))
      * (1 + tauC σ α w * u (tauC σ α w)) with hDdef
    have hX : ‖X‖ ≤ (51 / 1000000) * (77 / 1000000) * 12 := by
      rw [hXdef, norm_mul, norm_mul, hτc]
      have h2 : ‖τ - σ‖ ≤ 77 / 1000000 := by
        have hp : 8 * Real.pi * ‖α‖ ≤ 8 * Real.pi * (1 / 1000000) := by
          have h3 : Real.pi * ‖α‖ ≤ Real.pi * (1 / 1000000) :=
            mul_le_mul_of_nonneg_left hαs' (le_of_lt Real.pi_pos)
          linarith
        calc ‖τ - σ‖ ≤ ‖τ‖ + ‖σ‖ := norm_sub_le _ _
          _ ≤ 51 / 1000000 + 8 * Real.pi * (1 / 1000000) := by linarith [hτb, hσ8, hp]
          _ ≤ 77 / 1000000 := by
              have h3 : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
              nlinarith
      have h3 : ‖deriv u τ - u τ ^ 2‖ ≤ 12 := by
        have h4 : ‖deriv u τ‖ ≤ 8 := hderiv_le τ (by linarith [hτb])
        have h5 : ‖u τ ^ 2‖ ≤ 4 := by
          rw [norm_pow]
          nlinarith [huτb.2, norm_nonneg (u τ)]
        calc ‖deriv u τ - u τ ^ 2‖ ≤ ‖deriv u τ‖ + ‖u τ ^ 2‖ := norm_sub_le _ _
          _ ≤ 8 + 4 := by linarith
          _ = 12 := by norm_num
      have h5 : (0 : ℝ) ≤ 51 / 1000000 := by norm_num
      have h6 : (0 : ℝ) ≤ 77 / 1000000 := by norm_num
      exact mul_le_mul (mul_le_mul hτb h2 (norm_nonneg (τ - σ)) h5) h3
        (norm_nonneg (deriv u τ - u τ ^ 2)) (by positivity)
    have hD : (1 : ℝ) / 4 ≤ ‖D‖ := by
      have hDτ : ‖D‖ = ‖1 + τ * u τ - σ * u τ‖ * ‖1 + τ * u τ‖ := by
        simp only [hDdef, norm_mul, hτc]
      rw [hDτ]
      have h2 : 1 - ‖τ‖ * 2 ≤ ‖1 + τ * u τ‖ := by
        have h4 : ‖(1 : ℂ) + τ * u τ‖ = ‖1 - (-(τ * u τ))‖ := by ring_nf
        rw [h4]
        have h5 : 1 - ‖τ * u τ‖ ≤ ‖1 - (-(τ * u τ))‖ := by
          have := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
          rw [norm_one, norm_neg] at this
          linarith [le_abs_self (1 - ‖τ * u τ‖)]
        have h6 : ‖τ * u τ‖ ≤ 2 * ‖τ‖ := by
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right huτb.2 (norm_nonneg τ)
        linarith [h5, h6]
      have h3 : 1 - (‖τ * u τ‖ + ‖σ * u τ‖) ≤ ‖1 + τ * u τ - σ * u τ‖ := by
        have h4 : ‖1 + τ * u τ - σ * u τ‖ = ‖1 - (σ * u τ - τ * u τ)‖ := by ring_nf
        rw [h4]
        have h5 : |(1 : ℝ) - ‖σ * u τ - τ * u τ‖| ≤ ‖1 - (σ * u τ - τ * u τ)‖ := by
          simpa using abs_norm_sub_norm_le (1 : ℂ) (σ * u τ - τ * u τ)
        have h6 : ‖σ * u τ - τ * u τ‖ ≤ ‖τ * u τ‖ + ‖σ * u τ‖ := by
          have := norm_sub_le (σ * u τ) (τ * u τ); linarith
        linarith [h5, h6, le_abs_self (1 - ‖σ * u τ - τ * u τ‖)]
      have h4 : ‖τ * u τ‖ ≤ 2 * (51 / 1000000) := by
        rw [norm_mul]
        have := mul_le_mul huτb.2 hτb (norm_nonneg τ) (by norm_num : (0:ℝ) ≤ 2)
        linarith [this]
      have h5 : ‖σ * u τ‖ ≤ 2 * (8 * Real.pi * (1 / 1000000)) := by
        have h6 : 8 * Real.pi * ‖α‖ ≤ 8 * Real.pi * (1 / 1000000) :=
          mul_le_mul_of_nonneg_left hαs' (by positivity)
        calc ‖σ * u τ‖ ≤ (8 * Real.pi * ‖α‖) * 2 := by
              rw [norm_mul]
              exact mul_le_mul hσ8 huτb.2 (norm_nonneg (u τ))
                (by positivity : (0 : ℝ) ≤ 8 * Real.pi * ‖α‖)
          _ ≤ (8 * Real.pi * (1 / 1000000)) * 2 := by linarith
          _ = 2 * (8 * Real.pi * (1 / 1000000)) := by ring
      have h7 : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
      have h8 : (1 : ℝ) / 2 ≤ ‖1 + τ * u τ - σ * u τ‖ := by linarith [h3, h4, h5, h7]
      have h9 : (1 : ℝ) / 2 ≤ ‖1 + τ * u τ‖ := by linarith [h2, h4]
      nlinarith [h8, h9]
    have heq : 1 + X / D - 1 = X / D := by ring
    rw [heq, norm_div]
    calc ‖X‖ / ‖D‖ ≤ ((51 / 1000000) * (77 / 1000000) * 12) / ‖D‖ :=
          div_le_div_of_nonneg_right hX (norm_nonneg D)
      _ ≤ ((51 / 1000000) * (77 / 1000000) * 12) / (1 / 4) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD
      _ ≤ 1 / 32 := by norm_num
  exact ⟨hderivF.differentiableAt, hval, hderiv_bound⟩


/-- **Shishikura A.1.7(ii)** in the `1/32` form used by the FATOU contract: on the two gate regions
`Qreg (some ξ₁) (some (-ξ₁ + 1/α))` and `Qreg (some (ξ₁ - 1/α)) (some (-ξ₁))` the lift
`F_f = liftF u σ α` is a near-translation: `‖F_f w - (w+1)‖ ≤ 1/32` and `‖F_f'(w) - 1‖ ≤ 1/32`
there.  The hypotheses are: the normalisation `1 - σ u 0 = exp (2πiα)` (`= f'(0)`, without which
`σ = 0` makes `F_f` the identity), `α ≠ 0`, and the sector condition `MandelDim.InF1 α`
(`|Im α| < Re α`, the paper's class `𝓕₁`), which keeps the gate at distance `≳ ξ₁` from the lattice
`ℤ/α`.  The derivative bound on `u` needed for the second conjunct is derived from
`1/2 ≤ ‖u‖ ≤ 2` by Cauchy, hence not a hypothesis. -/
theorem gate :
    ∃ ξ₁ ε₀ ρ₀ : ℝ, 0 < ξ₁ ∧ 0 < ε₀ ∧ 0 < ρ₀ ∧
    ∀ {u : ℂ → ℂ} {σ α : ℂ} {ρ : ℝ}, ρ₀ ≤ ρ →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ) →
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * I * α) →
      ‖σ‖ ≤ ε₀ → ‖α‖ ≤ ε₀ → α ≠ 0 → MandelDim.InF1 α →
      MandelDim.NearTranslationOn (Work.Pert.liftF u σ α)
        (MandelDim.Qreg (some (ξ₁ : ℂ)) (some (-(ξ₁ : ℂ) + 1 / α))) ∧
      MandelDim.NearTranslationOn (Work.Pert.liftF u σ α)
        (MandelDim.Qreg (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ)))) := by
  refine ⟨(10 : ℝ) ^ 6, (10 : ℝ) ^ (-6 : ℤ), 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro u σ α ρ hρ hu hub hnorm hσs hαs hαne hinf
  have hξ : (0 : ℝ) < (10 : ℝ) ^ 6 := by norm_num
  have hpt : ∀ w : ℂ, (∀ k : ℤ, (10 : ℝ) ^ 6 / 2 ≤ ‖w - (k : ℂ) / α‖) →
      DifferentiableAt ℂ (liftF u σ α) w ∧ ‖liftF u σ α w - (w + 1)‖ ≤ 1 / 32 ∧
        ‖deriv (liftF u σ α) w - 1‖ ≤ 1 / 32 :=
    fun w hw => gate_point hρ hu hub hnorm hσs hαs hαne hinf hw
  constructor
  · refine ⟨fun w hw => (hpt w (fun k => gate_lattice_plus hξ hinf hw k)).1.differentiableWithinAt, ?_⟩
    exact fun w hw => (hpt w (fun k => gate_lattice_plus hξ hinf hw k)).2
  · refine ⟨fun w hw => (hpt w (fun k => gate_lattice_minus hξ hinf hw k)).1.differentiableWithinAt, ?_⟩
    exact fun w hw => (hpt w (fun k => gate_lattice_minus hξ hinf hw k)).2

end

end Work.Pert
