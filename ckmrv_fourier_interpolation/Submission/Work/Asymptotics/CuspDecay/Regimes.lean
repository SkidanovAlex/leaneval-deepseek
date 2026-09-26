import Mathlib
import Submission.Work.Asymptotics.CuspDecay.Defs
import Submission.Work.Asymptotics.CuspDecay.Core
import Submission.Work.Asymptotics.CuspDecay.Bounds
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.DeltaFun_upper_sharp

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics.CuspDecay

open Work.Kernels

/-- The split threshold: `Y - σ.im ≥ Kc` forces `‖q τ‖ ≤ 2⁻¹⁰⁰ ‖q σ‖`. -/
def Kc : ℝ := Real.log (2 ^ 100) / (2 * Real.pi)

lemma Kc_pos : 0 < Kc :=
  div_pos (Real.log_pos (by norm_num)) (by positivity)

lemma qParam_le_of_gap {a b : ℝ} (h : b + Kc ≤ a) :
    Real.exp (-(2 * Real.pi * a)) ≤ (1 / 2 : ℝ) ^ 100 * Real.exp (-(2 * Real.pi * b)) := by
  have hK : (0:ℝ) < 2 * Real.pi := by positivity
  have h1 : -(2 * Real.pi * a) = -(2 * Real.pi * b) + (-(2 * Real.pi * (a - b))) := by ring
  have h2 : Kc ≤ a - b := by linarith
  have h3 : 2 * Real.pi * Kc ≤ 2 * Real.pi * (a - b) := mul_le_mul_of_nonneg_left h2 hK.le
  have h4 : -(2 * Real.pi * (a - b)) ≤ -(2 * Real.pi * Kc) := by linarith
  have h5 : Real.exp (-(2 * Real.pi * (a - b))) ≤ Real.exp (-(2 * Real.pi * Kc)) :=
    Real.exp_le_exp.mpr h4
  have h6 : Real.exp (-(2 * Real.pi * Kc)) = (1 / 2 : ℝ) ^ 100 := by
    rw [Kc, mul_div_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0), Real.exp_neg,
      Real.exp_log (by positivity : (0:ℝ) < 2 ^ 100), ← inv_pow]
    norm_num
  rw [h1, Real.exp_add]
  calc Real.exp (-(2 * Real.pi * b)) * Real.exp (-(2 * Real.pi * (a - b)))
      ≤ Real.exp (-(2 * Real.pi * b)) * (1 / 2 : ℝ) ^ 100 := by
        rw [← h6]; exact mul_le_mul_of_nonneg_left h5 (Real.exp_nonneg _)
    _ = (1 / 2 : ℝ) ^ 100 * Real.exp (-(2 * Real.pi * b)) := by ring

lemma exp_three_ge : (20 : ℝ) ≤ Real.exp 3 := by
  have h1 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h3 : (Real.exp 1) ^ 3 = Real.exp 3 := by
    rw [pow_three, ← Real.exp_add, ← Real.exp_add]; norm_num
  have h4 : (2.7182818283:ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h1.le 3
  have h5 : (20:ℝ) ≤ (2.7182818283:ℝ) ^ 3 := by norm_num
  linarith [h3, h4, h5]

lemma exp_four_pi_ge : (40000 : ℝ) ≤ Real.exp (4 * Real.pi) := by
  have h12 : (12 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : Real.exp 12 ≤ Real.exp (4 * Real.pi) := Real.exp_le_exp.mpr h12
  have h2 : (Real.exp 1) ^ 12 = Real.exp 12 := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num
  have h3 : (2.7182818283:ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 12
  nlinarith [h1, h2, h3]

lemma qParam_le_half {u : ℍ} (h : 1 ≤ u.im) : ‖qParamFun u‖ ≤ 1 / 2 := by
  rw [norm_qParamFun]
  have h2 : (2:ℝ) ≤ Real.exp (2 * Real.pi) := by
    have := Real.add_one_le_exp (2 * Real.pi); linarith [Real.pi_gt_three]
  have h3 : Real.exp (-(2 * Real.pi * u.im)) ≤ Real.exp (-(2 * Real.pi)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h4 : Real.exp (-(2 * Real.pi)) = 1 / Real.exp (2 * Real.pi) := by
    rw [Real.exp_neg, one_div]
  have h5 : 1 / Real.exp (2 * Real.pi) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) h2
  linarith [h3, h4, h5]

lemma qParam_le_4e4 {u : ℍ} (h : 2 ≤ u.im) : ‖qParamFun u‖ ≤ 1 / 40000 := by
  rw [norm_qParamFun]
  have h2 : (40000:ℝ) ≤ Real.exp (4 * Real.pi) := exp_four_pi_ge
  have h3 : Real.exp (-(2 * Real.pi * u.im)) ≤ Real.exp (-(2 * Real.pi * 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h4 : Real.exp (-(2 * Real.pi * 2)) = 1 / Real.exp (4 * Real.pi) := by
    rw [show -(2 * Real.pi * 2) = -(4 * Real.pi) by ring, Real.exp_neg, one_div]
  have h5 : 1 / Real.exp (4 * Real.pi) ≤ 1 / 40000 :=
    one_div_le_one_div_of_le (by norm_num) h2
  linarith [h3, h4, h5]

/-- Explicit lower bound for `Δ`: `‖Δ τ‖ ≥ 2⁻²⁴ ‖q τ‖` for `Im τ ≥ 1`. -/
theorem DeltaFun_lower_ex2 (τ : ℍ) (hτ : 1 ≤ τ.im) :
    (1 / 2 : ℝ) ^ 24 * ‖qParamFun τ‖ ≤ ‖DeltaFun τ‖ := by
  have hΔ : DeltaFun τ = ModularForm.discriminant τ := by
    rw [show DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
  rw [hΔ, ModularForm.discriminant_eq_q_prod,
    show Function.Periodic.qParam 1 (τ : ℂ) = qParamFun τ
      from (Work.Asymptotics.qParamFun_eq_qParam τ).symm]
  have hP := Work.Asymptotics.tprod_eta_q_lower τ hτ
  have hmain : (1 / 2 : ℝ) ^ 24 * ‖qParamFun τ‖
      ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖ * ‖qParamFun τ‖ :=
    mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  calc (1 / 2 : ℝ) ^ 24 * ‖qParamFun τ‖
      ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖ * ‖qParamFun τ‖ := hmain
    _ = ‖qParamFun τ * ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖ := by
        rw [norm_mul]; ring

/-- `‖E₄ u‖ ≤ 10001` for `Im u ≥ 1`. -/
lemma E4_le_big {u : ℍ} (h : 1 ≤ u.im) : ‖E4Fun u‖ ≤ 10001 := by
  have h1 := E4Fun_sub_one_explicit h
  have h2 := qParam_le_half h
  have h3 : (20000:ℝ) * ‖qParamFun u‖ ≤ 10000 := by nlinarith [h2]
  have h4 : ‖E4Fun u - 1‖ ≤ 10000 := by linarith
  have h5 : ‖E4Fun u‖ ≤ ‖E4Fun u - 1‖ + 1 := by
    have := norm_add_le (E4Fun u - 1) (1:ℂ)
    simpa using this
  linarith

/-- `‖E₄ u‖ ≥ 1/2` for `Im u ≥ 2`. -/
lemma E4_ge_half {u : ℍ} (h : 2 ≤ u.im) : (1/2 : ℝ) ≤ ‖E4Fun u‖ := by
  have h1 := E4Fun_sub_one_explicit (le_trans (by norm_num) h)
  have h2 := qParam_le_4e4 h
  have h3 : (20000:ℝ) * ‖qParamFun u‖ ≤ 1/2 := by nlinarith [h2]
  have h4 : ‖E4Fun u - 1‖ ≤ 1/2 := by linarith
  have h5 : (1:ℝ) ≤ ‖E4Fun u‖ + ‖E4Fun u - 1‖ := by
    have h := norm_add_le (1 - E4Fun u) (E4Fun u)
    rw [sub_add_cancel, norm_one, norm_sub_rev] at h
    linarith
  linarith

/-- **Case A.**  If `σ.im + Kc ≤ τ.im` then `‖D₁(τ,z)‖ ≥ 2⁻²⁸ ‖q σ‖`. -/
theorem DOne_lower_fst (τ z : ℍ) (hτ : 2 ≤ τ.im) (hσ : 1 ≤ (sg z).im)
    (hgap : (sg z).im + Kc ≤ τ.im) :
    (1 / 2 : ℝ) ^ 28 * ‖qParamFun (sg z)‖ ≤ ‖DOne τ z‖ := by
  have hqτ : ‖qParamFun τ‖ ≤ (1/2:ℝ)^100 * ‖qParamFun (sg z)‖ := by
    simpa [norm_qParamFun] using qParam_le_of_gap hgap
  have hΔσ := DeltaFun_lower_ex2 (sg z) hσ
  have hE4τ := E4_ge_half hτ
  have hΔτ : ‖DeltaFun τ‖ ≤ 2 * ‖qParamFun τ‖ := by
    simpa [norm_qParamFun] using DeltaFun_upper_sharp τ (le_trans (by norm_num) hτ)
  have hE4σ := E4_le_big hσ
  have hqσ0 : (0:ℝ) ≤ ‖qParamFun (sg z)‖ := norm_nonneg _
  have hterm1 : (1 / 2 : ℝ) ^ 24 * (1/2:ℝ)^3 * ‖qParamFun (sg z)‖
      ≤ ‖DeltaFun (sg z)‖ * ‖E4Fun τ‖ ^ 3 := by
    calc (1/2:ℝ)^24 * (1/2:ℝ)^3 * ‖qParamFun (sg z)‖
        = ((1/2:ℝ)^24 * ‖qParamFun (sg z)‖) * (1/2:ℝ)^3 := by ring
      _ ≤ ‖DeltaFun (sg z)‖ * ‖E4Fun τ‖ ^ 3 :=
          mul_le_mul hΔσ (pow_le_pow_left₀ (by norm_num) hE4τ 3) (by positivity)
            (norm_nonneg _)
  have hterm2 : ‖DeltaFun τ‖ * ‖E4Fun (sg z)‖ ^ 3
      ≤ 2 * (1/2:ℝ)^100 * 10001^3 * ‖qParamFun (sg z)‖ := by
    calc ‖DeltaFun τ‖ * ‖E4Fun (sg z)‖ ^ 3
        ≤ (2 * ‖qParamFun τ‖) * 10001 ^ 3 :=
          mul_le_mul hΔτ (pow_le_pow_left₀ (norm_nonneg _) hE4σ 3) (by positivity)
            (by positivity)
      _ ≤ (2 * ((1/2:ℝ)^100 * ‖qParamFun (sg z)‖)) * 10001 ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
      _ = 2 * (1/2:ℝ)^100 * 10001^3 * ‖qParamFun (sg z)‖ := by ring
  have hnum : (2:ℝ) * (1/2:ℝ)^100 * 10001^3 ≤ (1/2:ℝ)^27 - (1/2:ℝ)^28 := by norm_num
  have hD : DOne τ z = DeltaFun (sg z) * E4Fun τ ^ 3 - DeltaFun τ * E4Fun (sg z) ^ 3 := rfl
  rw [hD]
  have htri : ‖DeltaFun (sg z) * E4Fun τ ^ 3 - DeltaFun τ * E4Fun (sg z) ^ 3‖
      ≥ ‖DeltaFun (sg z)‖ * ‖E4Fun τ‖ ^ 3 - ‖DeltaFun τ‖ * ‖E4Fun (sg z)‖ ^ 3 := by
    have h := norm_add_le (DeltaFun (sg z) * E4Fun τ ^ 3 - DeltaFun τ * E4Fun (sg z) ^ 3)
      (DeltaFun τ * E4Fun (sg z) ^ 3)
    rw [sub_add_cancel, norm_mul, norm_pow, norm_mul, norm_pow] at h
    linarith
  have hA : (1 / 2 : ℝ) ^ 24 * (1/2:ℝ)^3 * ‖qParamFun (sg z)‖
      = (1/2:ℝ)^27 * ‖qParamFun (sg z)‖ := by ring
  have hB : 2 * (1/2:ℝ)^100 * 10001^3 * ‖qParamFun (sg z)‖
      ≤ ((1/2:ℝ)^27 - (1/2:ℝ)^28) * ‖qParamFun (sg z)‖ :=
    mul_le_mul_of_nonneg_right hnum hqσ0
  linarith [htri, hterm1, hterm2, hA, hB]

/-- **Case B.**  If `τ.im + Kc ≤ σ.im` then `‖D₁(τ,z)‖ ≥ 2⁻²⁸ ‖q τ‖`. -/
theorem DOne_lower_snd (τ z : ℍ) (hτ : 2 ≤ τ.im) (hσ : 1 ≤ (sg z).im)
    (hgap : τ.im + Kc ≤ (sg z).im) :
    (1 / 2 : ℝ) ^ 28 * ‖qParamFun τ‖ ≤ ‖DOne τ z‖ := by
  have hqσ : ‖qParamFun (sg z)‖ ≤ (1/2:ℝ)^100 * ‖qParamFun τ‖ := by
    simpa [norm_qParamFun] using qParam_le_of_gap hgap
  have hΔτ := DeltaFun_lower_ex2 τ (le_trans (by norm_num) hτ)
  have hE4σ : (1/2:ℝ) ≤ ‖E4Fun (sg z)‖ :=
    E4_ge_half (le_trans (by linarith [Kc_pos]) hgap)
  have hΔσ : ‖DeltaFun (sg z)‖ ≤ 2 * ‖qParamFun (sg z)‖ := by
    simpa [norm_qParamFun] using DeltaFun_upper_sharp (sg z) hσ
  have hE4τ := E4_le_big (le_trans (by norm_num) hτ)
  have hqτ0 : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hterm1 : (1 / 2 : ℝ) ^ 27 * ‖qParamFun τ‖ ≤ ‖DeltaFun τ‖ * ‖E4Fun (sg z)‖ ^ 3 := by
    have h27 : (1/2:ℝ)^24 * (1/2:ℝ)^3 = (1/2:ℝ)^27 := by norm_num
    rw [← h27]
    calc (1/2:ℝ)^24 * (1/2:ℝ)^3 * ‖qParamFun τ‖
        = ((1/2:ℝ)^24 * ‖qParamFun τ‖) * (1/2:ℝ)^3 := by ring
      _ ≤ ‖DeltaFun τ‖ * ‖E4Fun (sg z)‖ ^ 3 :=
          mul_le_mul hΔτ (pow_le_pow_left₀ (by norm_num) hE4σ 3) (by positivity)
            (norm_nonneg _)
  have hterm2 : ‖DeltaFun (sg z)‖ * ‖E4Fun τ‖ ^ 3
      ≤ ((1/2:ℝ)^27 - (1/2:ℝ)^28) * ‖qParamFun τ‖ := by
    have hb : 2 * (1/2:ℝ)^100 * 10001^3 ≤ (1/2:ℝ)^27 - (1/2:ℝ)^28 := by norm_num
    calc ‖DeltaFun (sg z)‖ * ‖E4Fun τ‖ ^ 3
        ≤ (2 * ‖qParamFun (sg z)‖) * 10001 ^ 3 :=
          mul_le_mul hΔσ (pow_le_pow_left₀ (norm_nonneg _) hE4τ 3) (by positivity)
            (by positivity)
      _ ≤ (2 * ((1/2:ℝ)^100 * ‖qParamFun τ‖)) * 10001 ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
      _ = 2 * (1/2:ℝ)^100 * 10001^3 * ‖qParamFun τ‖ := by ring
      _ ≤ ((1/2:ℝ)^27 - (1/2:ℝ)^28) * ‖qParamFun τ‖ :=
          mul_le_mul_of_nonneg_right hb hqτ0
  have hD : DOne τ z = DeltaFun (sg z) * E4Fun τ ^ 3 - DeltaFun τ * E4Fun (sg z) ^ 3 := rfl
  rw [hD]
  have htri : ‖DeltaFun (sg z) * E4Fun τ ^ 3 - DeltaFun τ * E4Fun (sg z) ^ 3‖
      ≥ ‖DeltaFun τ‖ * ‖E4Fun (sg z)‖ ^ 3 - ‖DeltaFun (sg z)‖ * ‖E4Fun τ‖ ^ 3 := by
    have h := norm_add_le (DeltaFun τ * E4Fun (sg z) ^ 3 - DeltaFun (sg z) * E4Fun τ ^ 3)
      (DeltaFun (sg z) * E4Fun τ ^ 3)
    rw [sub_add_cancel, norm_mul, norm_pow, norm_mul, norm_pow] at h
    have he : ‖DeltaFun (sg z) * E4Fun τ ^ 3 - DeltaFun τ * E4Fun (sg z) ^ 3‖
        = ‖DeltaFun τ * E4Fun (sg z) ^ 3 - DeltaFun (sg z) * E4Fun τ ^ 3‖ :=
      norm_sub_rev _ _
    rw [he]
    linarith
  linarith [htri, hterm1, hterm2]

end Work.Asymptotics.CuspDecay
