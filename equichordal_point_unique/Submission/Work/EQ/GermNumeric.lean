import Mathlib
import Submission.Work.EQ.GermSetup

/-! Numeric bounds on the parameters `λ = eqLam a`, `r = germR a` used in the
contraction estimate for the fixed point operator `ThetaOf`. -/

namespace Work.EQ

open Complex Metric Filter

variable {a : ℝ}

lemma kapC_eq_sub (a : ℝ) : kapC a = ((eqLam a)⁻¹ - eqLam a : ℝ) := rfl

lemma kapC_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 ≤ (eqLam a)⁻¹ - eqLam a := by
  have h0 := eqLam_pos ha0 ha1
  have h1 := eqLam_lt_one ha0 ha1
  have : 1 ≤ (eqLam a)⁻¹ := by
    rw [one_le_inv₀ h0]; exact le_of_lt h1
  linarith

lemma gLipK_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 ≤ gLipK a := by
  have h0 := eqLam_pos ha0 ha1
  have hk := kapC_nonneg ha0 ha1
  have ha : 0 ≤ a := le_of_lt ha0
  have hX : 0 ≤ 1 + ((eqLam a) ^ 3)⁻¹ := by positivity
  have hY : 0 ≤ 1 + (eqLam a) ^ 3 := by positivity
  have hZ : 0 ≤ 1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a) := by linarith
  unfold gLipK
  nlinarith [mul_nonneg ha hk, mul_nonneg hX hY, mul_nonneg ha hX, mul_nonneg ha hZ]

/-- `λ^4 * ((eqLam a)^3)⁻¹ = eqLam a`. -/
lemma lam_pow_four_mul_inv_pow_three {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (eqLam a) ^ 4 * ((eqLam a) ^ 3)⁻¹ = eqLam a := by
  have hne : (eqLam a) ^ 3 ≠ 0 := by
    have := eqLam_pos ha0 ha1
    positivity
  calc (eqLam a) ^ 4 * ((eqLam a) ^ 3)⁻¹
      = eqLam a * ((eqLam a) ^ 3 * ((eqLam a) ^ 3)⁻¹) := by ring
    _ = eqLam a * 1 := by rw [mul_inv_cancel₀ hne]
    _ = eqLam a := by ring

lemma lam_pow_four_mul_gLipK_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (eqLam a) ^ 4 * gLipK a ≤ 100 := by
  have h0 := eqLam_pos ha0 ha1
  have h1 := eqLam_lt_one ha0 ha1
  have h0' : 0 ≤ eqLam a := le_of_lt h0
  have h1' : eqLam a ≤ 1 := le_of_lt h1
  have ha0' : 0 ≤ a := le_of_lt ha0
  have ha1' : a ≤ 1 := le_of_lt ha1
  have h4 : (eqLam a) ^ 4 ≤ 1 := pow_le_one₀ h0' h1'
  have h3 : (eqLam a) ^ 3 ≤ 1 := pow_le_one₀ h0' h1'
  have key := lam_pow_four_mul_inv_pow_three ha0 ha1
  have e1 : (eqLam a) ^ 4 * (1 + ((eqLam a) ^ 3)⁻¹) = (eqLam a) ^ 4 + eqLam a := by
    rw [mul_add, mul_one, key]
  have e2 : (eqLam a) ^ 4 * ((eqLam a)⁻¹ - eqLam a) ≤ 1 := by
    have hne : eqLam a ≠ 0 := ne_of_gt h0
    have h1m : (eqLam a) ^ 4 * (eqLam a)⁻¹ = (eqLam a) ^ 3 := by
      calc (eqLam a) ^ 4 * (eqLam a)⁻¹
          = (eqLam a) ^ 3 * ((eqLam a) * (eqLam a)⁻¹) := by ring
        _ = (eqLam a) ^ 3 * 1 := by rw [mul_inv_cancel₀ hne]
        _ = (eqLam a) ^ 3 := by ring
    have heq : (eqLam a) ^ 4 * ((eqLam a)⁻¹ - eqLam a)
        = (eqLam a) ^ 3 - (eqLam a) ^ 5 := by
      rw [mul_sub, h1m]; ring
    rw [heq]
    have h5 : 0 ≤ (eqLam a) ^ 5 := by positivity
    linarith
  have hexp : (eqLam a) ^ 4 * gLipK a
      = 12 * a * ((eqLam a) ^ 4 * ((eqLam a)⁻¹ - eqLam a))
        + 2 * ((eqLam a) ^ 4 * (1 + ((eqLam a) ^ 3)⁻¹)) * (1 + (eqLam a) ^ 3)
        + 2 * a * ((eqLam a) ^ 4 * (1 + ((eqLam a) ^ 3)⁻¹))
        + 4 * a * ((eqLam a) ^ 4 * (1 + ((eqLam a) ^ 3)⁻¹)
            + (eqLam a) ^ 4 * ((eqLam a)⁻¹ - eqLam a))
        + a * ((eqLam a) ^ 4 * (1 + ((eqLam a) ^ 3)⁻¹)) := by
    unfold gLipK; ring
  rw [hexp, e1]
  have hX0 : 0 ≤ (eqLam a) ^ 4 * ((eqLam a)⁻¹ - eqLam a) :=
    mul_nonneg (by positivity) (kapC_nonneg ha0 ha1)
  have hA : (eqLam a) ^ 4 + eqLam a ≤ 2 := by linarith
  have hA0 : 0 ≤ (eqLam a) ^ 4 + eqLam a := by positivity
  have hB : 1 + (eqLam a) ^ 3 ≤ 2 := by linarith
  have hB0 : 0 ≤ 1 + (eqLam a) ^ 3 := by positivity
  have hC : (eqLam a) ^ 4 + eqLam a + (eqLam a) ^ 4 * ((eqLam a)⁻¹ - eqLam a) ≤ 3 := by
    linarith
  have hC0 : 0 ≤ (eqLam a) ^ 4 + eqLam a + (eqLam a) ^ 4 * ((eqLam a)⁻¹ - eqLam a) := by
    linarith
  have q1 : a * ((eqLam a) ^ 4 * ((eqLam a)⁻¹ - eqLam a)) ≤ 1 := by
    have := mul_le_mul ha1' e2 hX0 zero_le_one
    linarith
  have q2 : ((eqLam a) ^ 4 + eqLam a) * (1 + (eqLam a) ^ 3) ≤ 4 := by
    have := mul_le_mul hA hB hB0 (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have q3 : a * ((eqLam a) ^ 4 + eqLam a) ≤ 2 := by
    have := mul_le_mul ha1' hA hA0 zero_le_one
    linarith
  have q4 : a * ((eqLam a) ^ 4 + eqLam a + (eqLam a) ^ 4 * ((eqLam a)⁻¹ - eqLam a)) ≤ 3 := by
    have := mul_le_mul ha1' hC hC0 zero_le_one
    linarith
  linarith


/-- The contraction factor: `λ⁴ r² gLipK / ((1-λ)² (1+λ²)) ≤ 1/2`. -/
lemma lam_four_mul_germR_sq_mul_gLipK_div_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (eqLam a) ^ 4 * (germR a) ^ 2 * gLipK a
      / ((1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2)) ≤ 1 / 2 := by
  have h0 := eqLam_pos ha0 ha1
  have h1 := eqLam_lt_one ha0 ha1
  have hden : a ^ 2 ≤ (1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2) := by
    rw [show (1 - eqLam a) ^ 2 = a ^ 2 * (1 + eqLam a) ^ 2 by
      rw [one_sub_eqLam_gs ha0]; ring]
    have h2 : (1 : ℝ) ≤ (1 + eqLam a) ^ 2 := by nlinarith
    have h3 : (1 : ℝ) ≤ 1 + (eqLam a) ^ 2 := by nlinarith [sq_nonneg (eqLam a)]
    have h23 : (1 : ℝ) ≤ (1 + eqLam a) ^ 2 * (1 + (eqLam a) ^ 2) := by nlinarith
    nlinarith [sq_nonneg a, h23]
  have hr2 : (germR a) ^ 2 ≤ a ^ 2 / 10 ^ 4 := by
    have := germR_le_a_div a
    have hr0 : 0 ≤ germR a := le_of_lt (germR_pos ha0 ha1)
    nlinarith
  have hK := lam_pow_four_mul_gLipK_le ha0 ha1
  have hK0 := gLipK_nonneg ha0 ha1
  have hnum : (eqLam a) ^ 4 * (germR a) ^ 2 * gLipK a ≤ a ^ 2 / 100 := by
    have h4 : 0 ≤ (eqLam a) ^ 4 := by positivity
    have hstep : (eqLam a) ^ 4 * (germR a) ^ 2 ≤ (eqLam a) ^ 4 * (a ^ 2 / 10 ^ 4) :=
      mul_le_mul_of_nonneg_left hr2 h4
    nlinarith [hstep, hK, hK0, h4]
  have hstep : (eqLam a) ^ 4 * (germR a) ^ 2 * gLipK a
      / ((1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2)) ≤ (a ^ 2 / 100) / a ^ 2 := by
    have hDpos : (0:ℝ) < (1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2) := by positivity
    calc (eqLam a) ^ 4 * (germR a) ^ 2 * gLipK a
          / ((1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2))
        ≤ (a ^ 2 / 100) / ((1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2)) :=
          div_le_div_of_nonneg_right hnum hDpos.le
      _ ≤ (a ^ 2 / 100) / a ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have ha2 : (a ^ 2 / 100) / a ^ 2 = 1 / 100 := by
    field_simp
  rw [ha2] at hstep
  linarith

end Work.EQ
