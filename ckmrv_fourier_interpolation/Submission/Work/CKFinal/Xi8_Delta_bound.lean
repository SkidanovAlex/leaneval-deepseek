import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.KPlusFunnel.Atoms
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.ZAtomsThird.cusp_forms
import Submission.Work.Asymptotics.ZAtomsThird.first_order

namespace Work.CKFinal

open UpperHalfPlane

set_option maxHeartbeats 1600000

/-- The `τ`-atom `φ₈ = E₄(τE₆ - 2φ₀E₄) + E₆φ₂` is `O((1 + ‖τ‖) q(τ))` on `{Im τ ≥ 1/3}`. -/
theorem phi8_bound_third :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im →
      ‖Work.Asymptotics.phi8 τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨Cc, hCc, hc1, hc2, hc3, hc4⟩ := Work.Asymptotics.ZAtomsThird.cusp_forms
  obtain ⟨C1, hC1, hE2, hE4, hE6, hD⟩ := Work.Asymptotics.ZAtomsThird.first_order
  refine ⟨(1 + C1 + 6 / Real.pi) * Cc + (1 + C1) * Cc + 1, ?_, fun τ hτ => ?_⟩
  · have h6p : (0 : ℝ) < 6 / Real.pi := by positivity
    have h1 : 0 < 1 + C1 + 6 / Real.pi := by linarith
    have h2 : 0 < 1 + C1 := by linarith
    nlinarith [mul_pos h1 hCc, mul_pos h2 hCc]
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 :=
    le_trans (Work.Asymptotics.norm_qParam_le_third hτ) (by norm_num)
  have hτn0 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have hτn : ‖(τ : ℂ)‖ ≤ 1 + ‖(τ : ℂ)‖ := by linarith [hτn0]
  have hE2b : ‖Work.Kernels.E2Fun τ‖ ≤ 1 + C1 := by
    have h := hE2 τ hτ
    calc ‖Work.Kernels.E2Fun τ‖ = ‖(Work.Kernels.E2Fun τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E2Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hq1, hC1.le]
      _ = 1 + C1 := by ring
  have hE4b : ‖Work.Kernels.E4Fun τ‖ ≤ 1 + C1 := by
    have h := hE4 τ hτ
    calc ‖Work.Kernels.E4Fun τ‖ = ‖(Work.Kernels.E4Fun τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E4Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hq1, hC1.le]
      _ = 1 + C1 := by ring
  have h6pi : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le]
  have h6p : (0 : ℝ) ≤ 6 / Real.pi := by positivity
  have h1c : (0 : ℝ) ≤ 1 + C1 + 6 / Real.pi := by linarith
  have hph0 : ‖Work.Kernels.phi0 τ - 3 * Complex.I / (Real.pi : ℂ)‖
      ≤ (1 + C1 + 6 / Real.pi) * (1 + ‖(τ : ℂ)‖) := by
    have heq : Work.Kernels.phi0 τ - 3 * Complex.I / (Real.pi : ℂ)
        = (τ : ℂ) * Work.Kernels.E2Fun τ - 6 * Complex.I / (Real.pi : ℂ) := by
      simp only [Work.Kernels.phi0]; ring
    rw [heq]
    calc ‖(τ : ℂ) * Work.Kernels.E2Fun τ - 6 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(τ : ℂ) * Work.Kernels.E2Fun τ‖ + ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ :=
          norm_sub_le _ _
      _ = ‖(τ : ℂ)‖ * ‖Work.Kernels.E2Fun τ‖ + 6 / Real.pi := by rw [norm_mul, h6pi]
      _ ≤ ‖(τ : ℂ)‖ * (1 + C1) + 6 / Real.pi := by
          have := mul_le_mul_of_nonneg_left hE2b hτn0
          linarith
      _ ≤ (1 + C1 + 6 / Real.pi) * (1 + ‖(τ : ℂ)‖) := by
          nlinarith [hτn0, hC1.le, h6p]
  rw [Work.Asymptotics.phi8_eq τ]
  have h1 : ‖(Work.Kernels.phi0 τ - 3 * Complex.I / (Real.pi : ℂ))
        * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2)‖
      ≤ (1 + C1 + 6 / Real.pi) * (1 + ‖(τ : ℂ)‖) * (Cc * ‖Work.Kernels.qParamFun τ‖) := by
    rw [norm_mul]
    exact mul_le_mul hph0 (hc2 τ hτ) (norm_nonneg _)
      (mul_nonneg h1c (by linarith [hτn0]))
  have h2 : ‖(τ : ℂ) * Work.Kernels.E4Fun τ
        * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)‖
      ≤ (1 + C1) * (1 + ‖(τ : ℂ)‖) * (Cc * ‖Work.Kernels.qParamFun τ‖) := by
    rw [show (τ : ℂ) * Work.Kernels.E4Fun τ
          * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)
        = (τ : ℂ) * (Work.Kernels.E4Fun τ
          * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)) by ring,
      norm_mul]
    have hinner : ‖Work.Kernels.E4Fun τ
          * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)‖
        ≤ (1 + C1) * (Cc * ‖Work.Kernels.qParamFun τ‖) := by
      rw [norm_mul]
      exact mul_le_mul hE4b (hc3 τ hτ) (norm_nonneg _) (by linarith [hC1])
    calc ‖(τ : ℂ)‖ * ‖Work.Kernels.E4Fun τ
            * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)‖
        ≤ (1 + ‖(τ : ℂ)‖) * ((1 + C1) * (Cc * ‖Work.Kernels.qParamFun τ‖)) :=
          mul_le_mul hτn hinner (norm_nonneg _) (by linarith [hτn0])
      _ = (1 + C1) * (1 + ‖(τ : ℂ)‖) * (Cc * ‖Work.Kernels.qParamFun τ‖) := by ring
  calc ‖(Work.Kernels.phi0 τ - 3 * Complex.I / (Real.pi : ℂ))
          * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2)
        - (τ : ℂ) * Work.Kernels.E4Fun τ
          * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)‖
      ≤ ‖(Work.Kernels.phi0 τ - 3 * Complex.I / (Real.pi : ℂ))
          * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2)‖
        + ‖(τ : ℂ) * Work.Kernels.E4Fun τ
          * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)‖ := norm_sub_le _ _
    _ ≤ (1 + C1 + 6 / Real.pi) * (1 + ‖(τ : ℂ)‖) * (Cc * ‖Work.Kernels.qParamFun τ‖)
        + (1 + C1) * (1 + ‖(τ : ℂ)‖) * (Cc * ‖Work.Kernels.qParamFun τ‖) := add_le_add h1 h2
    _ ≤ ((1 + C1 + 6 / Real.pi) * Cc + (1 + C1) * Cc + 1) * (1 + ‖(τ : ℂ)‖)
        * ‖Work.Kernels.qParamFun τ‖ := by
        have h0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ :=
          mul_nonneg (by linarith [hτn0]) hq0
        calc (1 + C1 + 6 / Real.pi) * (1 + ‖(τ : ℂ)‖) * (Cc * ‖Work.Kernels.qParamFun τ‖)
              + (1 + C1) * (1 + ‖(τ : ℂ)‖) * (Cc * ‖Work.Kernels.qParamFun τ‖)
            = ((1 + C1 + 6 / Real.pi) * Cc + (1 + C1) * Cc) * (1 + ‖(τ : ℂ)‖)
              * ‖Work.Kernels.qParamFun τ‖ := by ring
          _ ≤ ((1 + C1 + 6 / Real.pi) * Cc + (1 + C1) * Cc) * (1 + ‖(τ : ℂ)‖)
              * ‖Work.Kernels.qParamFun τ‖ + (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ :=
              le_add_of_nonneg_right h0
          _ = ((1 + C1 + 6 / Real.pi) * Cc + (1 + C1) * Cc + 1) * (1 + ‖(τ : ℂ)‖)
              * ‖Work.Kernels.qParamFun τ‖ := by ring

theorem Xi8_Delta_bound :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi8 τ z‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A *
            Real.exp (-(Real.pi * (2 * τ.im + z.im))) := by
  obtain ⟨Cc, hCc, hc1, hc2, hc3, hc4⟩ := Work.Asymptotics.ZAtomsThird.cusp_forms
  obtain ⟨C1, hC1, hE2, hE4, hE6, hD⟩ := Work.Asymptotics.ZAtomsThird.first_order
  obtain ⟨Cd, hCd, hdu⟩ := Work.Asymptotics.delta_upper_third
  obtain ⟨Cph, hCph, hph⟩ := phi8_bound_third
  set B : ℝ := 1 + C1 with hB
  set E : ℝ := 1 + C1 + 6 / Real.pi with hE
  set K : ℝ := Cd * B ^ 2 * Cph + Cd * B ^ 3 * Cc + 2 * Cd * E * B ^ 2 * Cc with hK
  have h6p : (0 : ℝ) < 6 / Real.pi := by positivity
  have h36 : 3 / Real.pi ≤ 6 / Real.pi :=
    div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le
  have hB0 : 0 < B := by rw [hB]; linarith
  have hE0 : 0 < E := by rw [hE]; linarith
  have hBe : B ≤ E := by rw [hB, hE]; linarith
  have h3E : 3 / Real.pi ≤ E := by rw [hE]; linarith
  have hK0 : 0 < K := by
    rw [hK]
    have h1 : 0 < Cd * B ^ 2 * Cph := mul_pos (mul_pos hCd (pow_pos hB0 2)) hCph
    have h2 : 0 < Cd * B ^ 3 * Cc := mul_pos (mul_pos hCd (pow_pos hB0 3)) hCc
    have h3 : 0 < 2 * Cd * E * B ^ 2 * Cc :=
      mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hCd) hE0) (pow_pos hB0 2)) hCc
    linarith
  refine ⟨K, 1, hK0, by norm_num, fun τ z hτ hz => ?_⟩
  have hDt : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hqt0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hqz0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hqt1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 :=
    le_trans (Work.Asymptotics.norm_qParam_le_third hτ) (by norm_num)
  have hqz1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 :=
    le_trans (Work.Asymptotics.norm_qParam_le_third hz) (by norm_num)
  have hτn0 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have hzn0 : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have hE4t : ‖Work.Kernels.E4Fun τ‖ ≤ B := by
    have h := hE4 τ hτ
    calc ‖Work.Kernels.E4Fun τ‖ = ‖(Work.Kernels.E4Fun τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E4Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hqt1, hC1.le]
      _ = B := by rw [hB]; ring
  have hE6t : ‖Work.Kernels.E6Fun τ‖ ≤ B := by
    have h := hE6 τ hτ
    calc ‖Work.Kernels.E6Fun τ‖ = ‖(Work.Kernels.E6Fun τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E6Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hqt1, hC1.le]
      _ = B := by rw [hB]; ring
  have hE4z : ‖Work.Kernels.E4Fun z‖ ≤ B := by
    have h := hE4 z hz
    calc ‖Work.Kernels.E4Fun z‖ = ‖(Work.Kernels.E4Fun z - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E4Fun z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun z‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hqz1, hC1.le]
      _ = B := by rw [hB]; ring
  have hE2t : ‖Work.Kernels.E2Fun τ‖ ≤ B := by
    have h := hE2 τ hτ
    calc ‖Work.Kernels.E2Fun τ‖ = ‖(Work.Kernels.E2Fun τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E2Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hqt1, hC1.le]
      _ = B := by rw [hB]; ring
  have h3pi : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le]
  have hphi0 : ‖Work.Kernels.phi0 τ‖ ≤ E * (1 + ‖(τ : ℂ)‖) := by
    have heq : Work.Kernels.phi0 τ
        = (τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := by
      simp only [Work.Kernels.phi0]
    rw [heq]
    calc ‖(τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(τ : ℂ) * Work.Kernels.E2Fun τ‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ :=
          norm_sub_le _ _
      _ = ‖(τ : ℂ)‖ * ‖Work.Kernels.E2Fun τ‖ + 3 / Real.pi := by rw [norm_mul, h3pi]
      _ ≤ ‖(τ : ℂ)‖ * B + 3 / Real.pi := by
          have := mul_le_mul_of_nonneg_left hE2t hτn0
          linarith
      _ ≤ ‖(τ : ℂ)‖ * E + E := add_le_add (mul_le_mul_of_nonneg_left hBe hτn0) h3E
      _ = E * (1 + ‖(τ : ℂ)‖) := by ring
  have hdelz : ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖
      ≤ Cc * ‖Work.Kernels.qParamFun z‖ := hc1 z hz
  have hepsz : ‖Work.Kernels.E2Fun z * Work.Kernels.E6Fun z - Work.Kernels.E4Fun z ^ 2‖
      ≤ Cc * ‖Work.Kernels.qParamFun z‖ := hc2 z hz
  have hDzb : ‖Work.Kernels.DeltaFun z‖ ≤ Cd * ‖Work.Kernels.qParamFun z‖ := hdu z hz
  have hDtb : ‖Work.Kernels.DeltaFun τ‖ ≤ Cd * ‖Work.Kernels.qParamFun τ‖ := hdu τ hτ
  have hph8 : ‖Work.Asymptotics.phi8 τ‖
      ≤ Cph * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ := hph τ hτ
  set A1 : ℂ := Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 2 * Work.Asymptotics.phi8 τ
    with hA1
  set A2 : ℂ := (τ : ℂ) * Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
            * Work.Kernels.E4Fun z ^ 2
            * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) with hA2
  set A3 : ℂ := 2 * Work.Kernels.DeltaFun τ * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
            * Work.Kernels.E4Fun z
            * (Work.Kernels.E2Fun z * Work.Kernels.E6Fun z - Work.Kernels.E4Fun z ^ 2) with hA3
  have hid : Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi8 τ z = A1 - A2 - A3 := by
    rw [hA1, hA2, hA3]
    rw [Work.Asymptotics.Xi8_cancelled τ z hDt hDz]
    field_simp
  have hT1 : ‖A1‖ ≤ (Cd * B ^ 2 * Cph) * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
          * ‖Work.Kernels.qParamFun z‖ := by
    rw [hA1]
    simp only [norm_mul, norm_pow]
    have hsq : ‖Work.Kernels.E4Fun τ‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE4t 2
    have hb1 : (0 : ℝ) ≤ (Cd * ‖Work.Kernels.qParamFun z‖) * B ^ 2 :=
      mul_nonneg (mul_nonneg hCd.le hqz0) (pow_nonneg hB0.le 2)
    have hb2 : (0 : ℝ) ≤ Cph * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ :=
      mul_nonneg (mul_nonneg hCph.le (by linarith [hτn0])) hqt0
    calc ‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.E4Fun τ‖ ^ 2 * ‖Work.Asymptotics.phi8 τ‖
        ≤ (Cd * ‖Work.Kernels.qParamFun z‖) * B ^ 2
            * (Cph * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖) :=
          mul_le_mul (mul_le_mul hDzb hsq (by positivity) (mul_nonneg hCd.le hqz0))
            hph8 (norm_nonneg _) hb1
      _ = (Cd * B ^ 2 * Cph) * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hT2 : ‖A2‖ ≤ (Cd * B ^ 3 * Cc) * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
          * ‖Work.Kernels.qParamFun z‖ := by
    rw [hA2]
    simp only [norm_mul, norm_pow]
    have hsq : ‖Work.Kernels.E4Fun z‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE4z 2
    have hτn : ‖(τ : ℂ)‖ ≤ 1 + ‖(τ : ℂ)‖ := by linarith [hτn0]
    have h11 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith [hτn0]
    have hcA : (0 : ℝ) ≤ Cd * ‖Work.Kernels.qParamFun τ‖ := mul_nonneg hCd.le hqt0
    have hcB : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖) :=
      mul_nonneg h11 hcA
    have hcC : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖) * B :=
      mul_nonneg hcB hB0.le
    have hcD : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖) * B * B ^ 2 :=
      mul_nonneg hcC (pow_nonneg hB0.le 2)
    have s1 : ‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖
        ≤ (1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖) :=
      mul_le_mul hτn hDtb (norm_nonneg _) h11
    have s2 : ‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E6Fun τ‖
        ≤ (1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖) * B :=
      mul_le_mul s1 hE6t (norm_nonneg _) hcB
    have s3 : ‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E6Fun τ‖
          * ‖Work.Kernels.E4Fun z‖ ^ 2
        ≤ (1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖) * B * B ^ 2 :=
      mul_le_mul s2 hsq (pow_nonneg (norm_nonneg _) 2) hcC
    have s4 : ‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E6Fun τ‖
          * ‖Work.Kernels.E4Fun z‖ ^ 2
          * ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖
        ≤ (1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖) * B * B ^ 2
            * (Cc * ‖Work.Kernels.qParamFun z‖) :=
      mul_le_mul s3 hdelz (norm_nonneg _) hcD
    calc ‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E6Fun τ‖
          * ‖Work.Kernels.E4Fun z‖ ^ 2
          * ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖
        ≤ (1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖) * B * B ^ 2
            * (Cc * ‖Work.Kernels.qParamFun z‖) := s4
      _ = (Cd * B ^ 3 * Cc) * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hT3 : ‖A3‖ ≤ (2 * Cd * E * B ^ 2 * Cc) * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
          * ‖Work.Kernels.qParamFun z‖ := by
    rw [hA3]
    simp only [norm_mul, Complex.norm_ofNat]
    have h11 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith [hτn0]
    have hcA : (0 : ℝ) ≤ Cd * ‖Work.Kernels.qParamFun τ‖ := mul_nonneg hCd.le hqt0
    have hEfac : (0 : ℝ) ≤ E * (1 + ‖(τ : ℂ)‖) := mul_nonneg hE0.le h11
    have hcB : (0 : ℝ) ≤ 2 * (Cd * ‖Work.Kernels.qParamFun τ‖) :=
      mul_nonneg (by norm_num) hcA
    have hcC : (0 : ℝ) ≤ 2 * (Cd * ‖Work.Kernels.qParamFun τ‖) * (E * (1 + ‖(τ : ℂ)‖)) :=
      mul_nonneg hcB hEfac
    have hcD : (0 : ℝ) ≤
        2 * (Cd * ‖Work.Kernels.qParamFun τ‖) * (E * (1 + ‖(τ : ℂ)‖)) * B :=
      mul_nonneg hcC hB0.le
    have hcE : (0 : ℝ) ≤
        2 * (Cd * ‖Work.Kernels.qParamFun τ‖) * (E * (1 + ‖(τ : ℂ)‖)) * B * B :=
      mul_nonneg hcD hB0.le
    have s1 : 2 * ‖Work.Kernels.DeltaFun τ‖
        ≤ 2 * (Cd * ‖Work.Kernels.qParamFun τ‖) :=
      mul_le_mul_of_nonneg_left hDtb (by norm_num)
    have s2 : 2 * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.phi0 τ‖
        ≤ 2 * (Cd * ‖Work.Kernels.qParamFun τ‖) * (E * (1 + ‖(τ : ℂ)‖)) :=
      mul_le_mul s1 hphi0 (norm_nonneg _) hcB
    have s3 : 2 * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.phi0 τ‖ * ‖Work.Kernels.E4Fun τ‖
        ≤ 2 * (Cd * ‖Work.Kernels.qParamFun τ‖) * (E * (1 + ‖(τ : ℂ)‖)) * B :=
      mul_le_mul s2 hE4t (norm_nonneg _) hcC
    have s4 : 2 * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.phi0 τ‖ * ‖Work.Kernels.E4Fun τ‖
          * ‖Work.Kernels.E4Fun z‖
        ≤ 2 * (Cd * ‖Work.Kernels.qParamFun τ‖) * (E * (1 + ‖(τ : ℂ)‖)) * B * B :=
      mul_le_mul s3 hE4z (norm_nonneg _) hcD
    have s5 : 2 * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.phi0 τ‖ * ‖Work.Kernels.E4Fun τ‖
          * ‖Work.Kernels.E4Fun z‖
          * ‖Work.Kernels.E2Fun z * Work.Kernels.E6Fun z - Work.Kernels.E4Fun z ^ 2‖
        ≤ 2 * (Cd * ‖Work.Kernels.qParamFun τ‖) * (E * (1 + ‖(τ : ℂ)‖)) * B * B
            * (Cc * ‖Work.Kernels.qParamFun z‖) :=
      mul_le_mul s4 hepsz (norm_nonneg _) hcE
    calc 2 * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.phi0 τ‖ * ‖Work.Kernels.E4Fun τ‖
          * ‖Work.Kernels.E4Fun z‖
          * ‖Work.Kernels.E2Fun z * Work.Kernels.E6Fun z - Work.Kernels.E4Fun z ^ 2‖
        ≤ 2 * (Cd * ‖Work.Kernels.qParamFun τ‖) * (E * (1 + ‖(τ : ℂ)‖)) * B * B
            * (Cc * ‖Work.Kernels.qParamFun z‖) := s5
      _ = (2 * Cd * E * B ^ 2 * Cc) * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hmain : ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi8 τ z‖
      ≤ K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ := by
    rw [hid]
    have htri : ‖A1 - A2 - A3‖ ≤ ‖A1‖ + ‖A2‖ + ‖A3‖ := by
      have s1 := norm_sub_le (A1 - A2) A3
      have s2 := norm_sub_le A1 A2
      linarith [s1, s2, norm_nonneg A1, norm_nonneg A2, norm_nonneg A3]
    calc ‖A1 - A2 - A3‖ ≤ ‖A1‖ + ‖A2‖ + ‖A3‖ := htri
      _ ≤ (Cd * B ^ 2 * Cph) * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
              * ‖Work.Kernels.qParamFun z‖
            + (Cd * B ^ 3 * Cc) * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
              * ‖Work.Kernels.qParamFun z‖
            + (2 * Cd * E * B ^ 2 * Cc) * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
              * ‖Work.Kernels.qParamFun z‖ := by linarith [hT1, hT2, hT3]
      _ = K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ := by
          rw [hK]; ring
  have hfinal : ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi8 τ z‖
      ≤ K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖) * Real.exp (-(Real.pi * (2 * τ.im + z.im))) := by
    have hX : (0 : ℝ) ≤
        K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg hK0.le (by linarith [hτn0])) hqt0) hqz0
    have hz1 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith [hzn0]
    have he2 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(Real.pi * z.im)) :=
      Real.exp_le_exp.mpr (by nlinarith [z.im_pos, Real.pi_pos])
    calc ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi8 τ z‖
        ≤ K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ := hmain
      _ ≤ K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖
            * (1 + ‖(z : ℂ)‖) := le_mul_of_one_le_right hX hz1
      _ = K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Kernels.qParamFun z‖ := by ring
      _ = K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖)
            * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * z.im))) := by
          rw [Work.Asymptotics.norm_qParamFun, Work.Asymptotics.norm_qParamFun]
          ring
      _ ≤ K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖)
            * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(Real.pi * z.im))) := by
          have hA : (0 : ℝ) ≤ K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖) :=
            mul_nonneg (mul_nonneg hK0.le (by linarith [hτn0])) (by linarith [hzn0])
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left he2 (Real.exp_pos _).le) hA
      _ = K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖)
            * Real.exp (-(Real.pi * (2 * τ.im + z.im))) := by
          rw [← Real.exp_add]
          congr 1
          ring
  simpa [Real.rpow_one] using hfinal

end Work.CKFinal
