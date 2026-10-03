import Mathlib
import Submission.Work.Pert.Basic

/-!
# PERT · `Work.Pert.scale_tau`: the `ρ_min`-parameterised `τ`-bound
-/

namespace Work.Pert

open MandelDim Complex

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

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

/-- Rounding: there is an integer within `1/2` of any real. -/
private lemma exists_int_abs_sub_le_half (x : ℝ) : ∃ k : ℤ, |x - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith


/-- **`Work.Pert.scale_tau`**: the `ρ_min`-parameterised `τ`-bound of Shishikura A.1.7(ii). -/
theorem scale_tau {σ α : ℂ} {ρmin : ℝ} {w : ℂ} (hρmin : 0 < ρmin)
    (hσ8 : ‖σ‖ ≤ 8 * Real.pi * ‖α‖) (hαs : ‖α‖ ≤ ρmin / 10 ^ 6)
    (hαne : α ≠ 0) (hinf : MandelDim.InF1 α)
    (hlat : ∀ k : ℤ, (10 ^ 6 / ρmin) / 2 ≤ ‖w - (k : ℂ) / α‖) :
    1 - Complex.exp (-(2 * Real.pi * I * α * w)) ≠ 0 ∧
    ‖Work.Pert.tauC σ α w‖ ≤ 16 * Real.pi * ρmin / 10 ^ 6 := by
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  -- the lattice spacing `C = 10^6/ρmin`
  set C : ℝ := 10 ^ 6 / ρmin with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hαC : ‖α‖ * C ≤ 1 := by
    rw [hC]
    calc ‖α‖ * (10 ^ 6 / ρmin) ≤ (ρmin / 10 ^ 6) * (10 ^ 6 / ρmin) :=
          mul_le_mul_of_nonneg_right hαs (by positivity)
      _ = 1 := by field_simp
  -- ## the point `δ` measuring the distance to the lattice
  set v : ℂ := -(α * w) with hv
  obtain ⟨k₀, hk₀⟩ := exists_int_abs_sub_le_half v.re
  set δ : ℂ := v - (k₀ : ℂ) with hδ
  have hδre : |δ.re| ≤ 1 / 2 := by
    have he : δ.re = v.re - (k₀ : ℝ) := by rw [hδ, Complex.sub_re]; simp
    rw [he]; exact hk₀
  have hδge : ‖α‖ * (C / 2) ≤ ‖δ‖ := by
    have h := hlat (-k₀)
    have hw : w - ((-k₀ : ℤ) : ℂ) / α = w + (k₀ : ℂ) / α := by
      rw [show ((-k₀ : ℤ) : ℂ) = -(k₀ : ℂ) by simp, neg_div, sub_neg_eq_add]
    rw [hw] at h
    have hkey : δ = -(α * (w + (k₀ : ℂ) / α)) := by
      rw [hδ, hv]; field_simp; ring
    rw [hkey, norm_neg, norm_mul, hC]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg α)
  have hexp_eq : Complex.exp (-(2 * Real.pi * I * α * w)) = Complex.exp (2 * Real.pi * I * δ) := by
    have h1 : -(2 * Real.pi * I * α * w) = 2 * Real.pi * I * v := by rw [hv]; ring
    rw [h1]
    have hvk : v = δ + (k₀ : ℂ) := by rw [hδ]; ring
    rw [hvk, show 2 * Real.pi * I * (δ + (k₀ : ℂ))
        = 2 * Real.pi * I * δ + (k₀ : ℂ) * (2 * Real.pi * I) by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hzeta : (1 : ℝ) / 2 ≤ ‖1 - Complex.exp (-(2 * Real.pi * I * α * w))‖ ∨
      ‖α‖ * (C / 2) ≤ ‖1 - Complex.exp (-(2 * Real.pi * I * α * w))‖ := by
    rw [hexp_eq]
    rcases le_total ‖δ‖ (1 / 2) with h | h
    · exact Or.inr (le_trans hδge (gate_exp_near δ h hδre))
    · exact Or.inl (gate_exp_far δ h hδre)
  have hζne : 1 - Complex.exp (-(2 * Real.pi * I * α * w)) ≠ 0 := by
    intro h0
    rcases hzeta with h | h
    · rw [h0, norm_zero] at h; norm_num at h
    · rw [h0, norm_zero] at h
      have hpos : 0 < ‖α‖ * (C / 2) := mul_pos hαpos (by linarith)
      linarith
  refine ⟨hζne, ?_⟩
  rw [tauC, norm_div]
  rcases hzeta with h | h
  · -- near case: `ζ ≥ 1/2`
    have h16 : 16 * Real.pi * ‖α‖ ≤ 16 * Real.pi * ρmin / 10 ^ 6 := by
      have h1 := mul_le_mul_of_nonneg_left hαs (by positivity : (0 : ℝ) ≤ 16 * Real.pi)
      calc 16 * Real.pi * ‖α‖ ≤ 16 * Real.pi * (ρmin / 10 ^ 6) := h1
        _ = 16 * Real.pi * ρmin / 10 ^ 6 := by ring
    calc ‖σ‖ / ‖1 - Complex.exp (-(2 * Real.pi * I * α * w))‖ ≤ ‖σ‖ / (1 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg σ) (by norm_num) h
      _ ≤ (8 * Real.pi * ‖α‖) / (1 / 2) := div_le_div_of_nonneg_right hσ8 (by norm_num)
      _ = 16 * Real.pi * ‖α‖ := by ring
      _ ≤ 16 * Real.pi * ρmin / 10 ^ 6 := h16
  · -- far case: `ζ ≥ ‖α‖ C/2`
    have hden : 0 < ‖α‖ * (C / 2) := mul_pos hαpos (by linarith)
    calc ‖σ‖ / ‖1 - Complex.exp (-(2 * Real.pi * I * α * w))‖ ≤ ‖σ‖ / (‖α‖ * (C / 2)) :=
          div_le_div_of_nonneg_left (norm_nonneg σ) hden h
      _ ≤ (8 * Real.pi * ‖α‖) / (‖α‖ * (C / 2)) :=
          div_le_div_of_nonneg_right hσ8 (le_of_lt hden)
      _ = 16 * Real.pi * ρmin / 10 ^ 6 := by
          rw [hC]
          field_simp
          ring

end

end Work.Pert
