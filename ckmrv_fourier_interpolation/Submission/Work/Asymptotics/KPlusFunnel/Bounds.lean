/-
# Funnel bounds for `Ξ₈` and `Ξ₂₄`

Using the cancelled forms of `Submission/Work/Asymptotics/KPlusFunnel/Atoms.lean` and the
growth of the `τ`-atoms on the funnel, this file bounds `Ξ₈(τ,z)` and `Ξ₂₄(τ,z)` by
`C (1 + ‖τ‖) ^ A ‖q(z)‖` on `{τ ∈ 𝒟 : 2 ≤ Im τ} × {Im z ≥ 1/3}`.

The `z`-estimates are taken as explicit hypotheses, so this file is independent of how the
`z`-cusp estimates are proved.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusFunnel.Atoms

namespace Work.Asymptotics

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

open Work.Kernels

/-! ## Helper lemmas for products -/

private lemma norm_mul3_le {a b c : ℂ} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) : ‖a * b * c‖ ≤ A * B * C := by
  rw [norm_mul, norm_mul]
  calc ‖a‖ * ‖b‖ * ‖c‖ ≤ A * B * ‖c‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul ha hb (norm_nonneg _) hA) (norm_nonneg _)
    _ ≤ A * B * C := mul_le_mul_of_nonneg_left hc (by positivity)

private lemma norm_mul4_le {a b c d : ℂ} {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) :
    ‖a * b * c * d‖ ≤ A * B * C * D := by
  have h3 : ‖a * b * c‖ ≤ A * B * C := norm_mul3_le hA hB hC ha hb hc
  rw [norm_mul]
  calc ‖a * b * c‖ * ‖d‖ ≤ A * B * C * D :=
        mul_le_mul h3 hd (norm_nonneg _) (by positivity)

private lemma norm_mul5_le {a b c d e : ℂ} {A B C D E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C)
    (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) : ‖a * b * c * d * e‖ ≤ A * B * C * D * E := by
  have h4 : ‖a * b * c * d‖ ≤ A * B * C * D := norm_mul4_le hA hB hC hD ha hb hc hd
  rw [norm_mul]
  calc ‖a * b * c * d‖ * ‖e‖ ≤ A * B * C * D * E :=
        mul_le_mul h4 he (norm_nonneg _) (by positivity)

/-! ## Auxiliary bounds -/

/-- `‖φ₀(τ)‖ ≤ (C + 3)(1 + ‖τ‖)` on the funnel when `‖E₂ τ‖ ≤ C` there. -/
theorem phi0_funnel_bound {C : ℝ} (hC : 0 ≤ C)
    (hE2 : ∀ τ : ℍ, Funnel τ → ‖E2Fun τ‖ ≤ C) :
    ∀ τ : ℍ, Funnel τ → ‖phi0 τ‖ ≤ (C + 3) * (1 + ‖(τ : ℂ)‖) := by
  intro τ hτ
  have ht0 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have h3 : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    congr 1
    simp
    all_goals positivity
  have hsplit : phi0 τ = (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := rfl
  rw [hsplit]
  have hle : ‖(τ : ℂ) * E2Fun τ‖ ≤ ‖(τ : ℂ)‖ * C := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hE2 τ hτ) ht0
  have hpi : 3 / Real.pi ≤ 3 := by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
  calc ‖(τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖(τ : ℂ) * E2Fun τ‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖(τ : ℂ)‖ * C + 3 := by rw [h3]; linarith
    _ ≤ (C + 3) * (1 + ‖(τ : ℂ)‖) := by nlinarith [ht0, hC]

/-- `‖φ₂(τ)‖ ≤ (C² + 6C)(1 + ‖τ‖)` on the funnel when `‖E₂ τ‖ ≤ C` there. -/
theorem phi2_funnel_bound {C : ℝ} (hC : 0 ≤ C)
    (hE2 : ∀ τ : ℍ, Funnel τ → ‖E2Fun τ‖ ≤ C) :
    ∀ τ : ℍ, Funnel τ → ‖phi2 τ‖ ≤ (C ^ 2 + 6 * C) * (1 + ‖(τ : ℂ)‖) := by
  intro τ hτ
  have ht0 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have hE := hE2 τ hτ
  have h6 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ) * E2Fun τ‖ ≤ 6 * C := by
    rw [show (6 : ℂ) * Complex.I / (Real.pi : ℂ) * E2Fun τ
        = ((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * E2Fun τ by ring, norm_mul]
    have hnorm : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
      rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
      congr 1
      simp
      all_goals positivity
    rw [hnorm]
    have hpi1 : (6 : ℝ) / Real.pi ≤ 6 := by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    calc (6 / Real.pi) * ‖E2Fun τ‖ ≤ 6 * C := by nlinarith [norm_nonneg (E2Fun τ), hC, hE]
      _ = 6 * C := rfl
  have hsplit : phi2 τ = (τ : ℂ) * E2Fun τ ^ 2 - 6 * Complex.I / (Real.pi : ℂ) * E2Fun τ := rfl
  rw [hsplit]
  have h2 : ‖(τ : ℂ) * E2Fun τ ^ 2‖ ≤ ‖(τ : ℂ)‖ * (C * C) := by
    rw [norm_mul, norm_pow, pow_two]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hE hE (norm_nonneg _) hC) ht0
  calc ‖(τ : ℂ) * E2Fun τ ^ 2 - 6 * Complex.I / (Real.pi : ℂ) * E2Fun τ‖
      ≤ ‖(τ : ℂ) * E2Fun τ ^ 2‖ + ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ) * E2Fun τ‖ :=
        norm_sub_le _ _
    _ ≤ ‖(τ : ℂ)‖ * (C * C) + 6 * C := add_le_add h2 h6
    _ ≤ (C ^ 2 + 6 * C) * (1 + ‖(τ : ℂ)‖) := by
        have : C ^ 2 = C * C := by ring
        nlinarith [ht0, hC]

/-! ## The bound for `Ξ₈` -/

theorem Xi8_bound_funnel
    (Cσ Cε CD B4 : ℝ) (hCσ : 0 < Cσ) (hCε : 0 < Cε) (hCD : 0 < CD) (hB4 : 0 < B4)
    (hσz : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cσ * ‖qParamFun z‖)
    (hεz : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E2Fun z * E6Fun z - E4Fun z ^ 2‖ ≤ Cε * ‖qParamFun z‖)
    (hE4z : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z‖ ≤ B4)
    (hDzu : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖DeltaFun z‖ ≤ CD * ‖qParamFun z‖) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (τ z : ℍ), Funnel τ → 1 / 3 ≤ z.im →
      ‖Xi8 τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖qParamFun z‖ := by
  obtain ⟨C4τ, hC4τ, hE4τ⟩ := exists_E4_Funnel_bound
  obtain ⟨C6τ, hC6τ, hE6τ⟩ := exists_E6_Funnel_bound
  obtain ⟨C2τ, hC2τ, hE2τ⟩ := exists_E2_Funnel_bound
  obtain ⟨CΔl, hCΔl, hΔl⟩ := exists_Delta_Funnel_lower
  obtain ⟨CΦ, hCΦ, hΦ⟩ := phi8_bound
  refine ⟨CD * C4τ ^ 2 * CΦ / CΔl + C6τ * B4 ^ 2 * Cσ + 2 * (C2τ + 3) * C4τ * B4 * Cε, 1,
    by positivity, zero_le_one, fun τ z hτ hz => ?_⟩
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have ht0 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have ht1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have hqτ : ‖qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := norm_qParamFun τ
  have hqτpos : 0 < ‖qParamFun τ‖ := by rw [hqτ]; exact Real.exp_pos _
  have hDτl : CΔl * ‖qParamFun τ‖ ≤ ‖DeltaFun τ‖ := by
    rw [hqτ]
    exact hΔl τ hτ
  have hφ0 := phi0_funnel_bound hC2τ.le hE2τ τ hτ
  rw [Xi8_cancelled τ z hDt hDz]
  rw [Real.rpow_one]
  have ht1' : ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ‖
      ≤ CD * C4τ ^ 2 * CΦ / CΔl * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    have hdiv : ‖DeltaFun z / DeltaFun τ‖ ≤ CD * ‖qParamFun z‖ / (CΔl * ‖qParamFun τ‖) := by
      rw [norm_div]
      have hinv : ‖(DeltaFun τ)⁻¹‖ ≤ (CΔl * ‖qParamFun τ‖)⁻¹ := by
        rw [norm_inv]
        exact (inv_le_inv₀ (lt_of_lt_of_le (mul_pos hCΔl hqτpos) hDτl) (mul_pos hCΔl hqτpos)).mpr hDτl
      calc ‖DeltaFun z‖ / ‖DeltaFun τ‖
          = ‖DeltaFun z‖ * ‖(DeltaFun τ)⁻¹‖ := by rw [norm_inv, div_eq_mul_inv]
        _ ≤ (CD * ‖qParamFun z‖) * (CΔl * ‖qParamFun τ‖)⁻¹ :=
            mul_le_mul (hDzu z hz) hinv (norm_nonneg _) (by positivity)
        _ = CD * ‖qParamFun z‖ / (CΔl * ‖qParamFun τ‖) := by rw [div_eq_mul_inv]
    have h4 : ‖E4Fun τ ^ 2‖ ≤ C4τ * C4τ := by
      rw [norm_pow, pow_two]
      exact mul_le_mul (hE4τ τ hτ) (hE4τ τ hτ) (norm_nonneg _) hC4τ.le
    calc ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ‖
        ≤ (CD * ‖qParamFun z‖ / (CΔl * ‖qParamFun τ‖)) * (C4τ * C4τ)
            * (CΦ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) :=
          norm_mul3_le (by positivity) (by positivity) (by positivity) hdiv h4 (hΦ τ hτ)
      _ = CD * C4τ ^ 2 * CΦ / CΔl * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
          field_simp
  have ht2' : ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
      ≤ C6τ * B4 ^ 2 * Cσ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    have h4 : ‖E4Fun z ^ 2‖ ≤ B4 * B4 := by
      rw [norm_pow, pow_two]
      exact mul_le_mul (hE4z z hz) (hE4z z hz) (norm_nonneg _) hB4.le
    calc ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
        ≤ (1 + ‖(τ : ℂ)‖) * C6τ * (B4 * B4) * (Cσ * ‖qParamFun z‖) :=
          norm_mul4_le (by positivity) hC6τ.le (by positivity) (by positivity)
            (by linarith [ht0]) (hE6τ τ hτ) h4 (hσz z hz)
      _ = C6τ * B4 ^ 2 * Cσ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  have ht3' : ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
      ≤ 2 * (C2τ + 3) * C4τ * B4 * Cε * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    calc ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
        ≤ 2 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) * C4τ * B4 * (Cε * ‖qParamFun z‖) :=
          norm_mul5_le (by norm_num) (by positivity) hC4τ.le hB4.le (by positivity)
            (by norm_num) hφ0 (hE4τ τ hτ) (hE4z z hz) (hεz z hz)
      _ = 2 * (C2τ + 3) * C4τ * B4 * Cε * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  calc ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ
          - (τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)
          - 2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
      ≤ (‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ‖
            + ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖)
          + ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖ := by
        have h1 := norm_sub_le (DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ)
          ((τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2))
        have h2 := norm_sub_le (DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ
          - (τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2))
          (2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2))
        linarith [norm_nonneg (DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ),
          norm_nonneg ((τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2))]
    _ ≤ (CD * C4τ ^ 2 * CΦ / CΔl * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
          + C6τ * B4 ^ 2 * Cσ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖)
          + 2 * (C2τ + 3) * C4τ * B4 * Cε * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ :=
        add_le_add (add_le_add ht1' ht2') ht3'
    _ = (CD * C4τ ^ 2 * CΦ / CΔl + C6τ * B4 ^ 2 * Cσ + 2 * (C2τ + 3) * C4τ * B4 * Cε)
          * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring

/-! ## The bound for `Ξ₂₄` -/

theorem Xi24_bound_funnel
    (Cσ CR Cq2 Cq4 Cj cΔ CΔu B4 : ℝ) (hCσ : 0 < Cσ) (hCR : 0 < CR)
    (hCq2 : 0 < Cq2) (hCq4 : 0 < Cq4) (hCj : 0 < Cj) (hcΔ : 0 < cΔ) (hCΔu : 0 < CΔu)
    (hB4 : 0 < B4)
    (hσz : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cσ * ‖qParamFun z‖)
    (hRz : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z‖
        ≤ CR * ‖qParamFun z‖ ^ 2)
    (hE2sq : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E2Fun z ^ 2 - 1‖ ≤ Cq2 * ‖qParamFun z‖)
    (hE4m1 : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z - 1‖ ≤ Cq4 * ‖qParamFun z‖)
    (hjzs : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288‖ ≤ Cj * ‖qParamFun z‖)
    (hE4z : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z‖ ≤ B4)
    (hDzl : ∀ z : ℍ, 1 / 3 ≤ z.im → cΔ * ‖qParamFun z‖ ≤ ‖DeltaFun z‖)
    (hDzu : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖DeltaFun z‖ ≤ CΔu * ‖qParamFun z‖) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (τ z : ℍ), Funnel τ → 1 / 3 ≤ z.im →
      ‖Xi24 τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖qParamFun z‖ := by
  obtain ⟨C4τ, hC4τ, hE4τ⟩ := exists_E4_Funnel_bound
  obtain ⟨C6τ, hC6τ, hE6τ⟩ := exists_E6_Funnel_bound
  obtain ⟨C2τ, hC2τ, hE2τ⟩ := exists_E2_Funnel_bound
  obtain ⟨Cjτ, hCjτ, hjτ⟩ := jFunnel_bound
  obtain ⟨CΦ, hCΦ, hΦ⟩ := phi8_bound
  obtain ⟨CΔu', hCΔu', hΔu'⟩ := deltaFunnel_upper
  refine ⟨6 * C4τ * CΦ * (Cσ * Cjτ + Cj) + 1728 * (C2τ + 3) * C4τ ^ 3 * (5 * Cσ + 2 * Cq2)
      + 1728 * C4τ ^ 2 * C6τ * Cq2 + 1728 * (C2τ ^ 2 + 6 * C2τ) * C4τ * C6τ * Cq4
      + 1728 * (C2τ + 3) * (CΔu + CΔu') * CR * B4 ^ 2 / cΔ, 1,
    by positivity, zero_le_one, fun τ z hτ hz => ?_⟩
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have ht0 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have ht1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have hq1τ : ‖qParamFun τ‖ ≤ 1 := norm_qParamFun_le_one' (Funnel.im_one hτ)
  have hqτpos : 0 < ‖qParamFun τ‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hDzpos : 0 < ‖qParamFun z‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hφ0 := phi0_funnel_bound hC2τ.le hE2τ τ hτ
  have hφ2 := phi2_funnel_bound hC2τ.le hE2τ τ hτ
  have hΔτu : ‖DeltaFun τ‖ ≤ (CΔu + CΔu') * ‖qParamFun τ‖ := by
    calc ‖DeltaFun τ‖ ≤ CΔu' * ‖qParamFun τ‖ := hΔu' τ hτ
      _ ≤ (CΔu + CΔu') * ‖qParamFun τ‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  rw [Xi24_cancelled τ z hDt hDz]
  rw [Real.rpow_one]
  -- `‖φ₈ τ‖ ‖j τ‖` without any division
  have hjprod : ‖phi8 τ‖ * ‖jInvariantFun τ‖ ≤ CΦ * (1 + ‖(τ : ℂ)‖) * Cjτ := by
    have hne : ‖qParamFun τ‖ ≠ 0 := ne_of_gt hqτpos
    calc ‖phi8 τ‖ * ‖jInvariantFun τ‖
        ≤ (CΦ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) * (Cjτ / ‖qParamFun τ‖) :=
          mul_le_mul (hΦ τ hτ) (hjτ τ hτ) (norm_nonneg _) (by positivity)
      _ = CΦ * (1 + ‖(τ : ℂ)‖) * Cjτ := by field_simp
  have hAB : ‖6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
        * (jInvariantFun τ - jInvariantFun z) + 1728 * E4Fun τ * phi8 τ‖
      ≤ 6 * C4τ * CΦ * (Cσ * Cjτ + Cj) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    have hkey : 6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
          * (jInvariantFun τ - jInvariantFun z) + 1728 * E4Fun τ * phi8 τ
        = 6 * E4Fun τ
          * (phi8 τ * ((E4Fun z - E2Fun z ^ 2) * jInvariantFun τ)
              + phi8 τ * (288 - jInvariantFun z * (E4Fun z - E2Fun z ^ 2))) := by ring
    rw [hkey, norm_mul]
    have h6 : ‖(6 : ℂ) * E4Fun τ‖ ≤ 6 * C4τ := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left (hE4τ τ hτ) (by norm_num)
    have hbracket : ‖phi8 τ * ((E4Fun z - E2Fun z ^ 2) * jInvariantFun τ)
          + phi8 τ * (288 - jInvariantFun z * (E4Fun z - E2Fun z ^ 2))‖
        ≤ (Cσ * Cjτ + Cj) * (CΦ * (1 + ‖(τ : ℂ)‖)) * ‖qParamFun z‖ := by
      have h1 : ‖phi8 τ * ((E4Fun z - E2Fun z ^ 2) * jInvariantFun τ)‖
          ≤ Cσ * Cjτ * (CΦ * (1 + ‖(τ : ℂ)‖)) * ‖qParamFun z‖ := by
        rw [norm_mul, norm_mul]
        calc ‖phi8 τ‖ * (‖E4Fun z - E2Fun z ^ 2‖ * ‖jInvariantFun τ‖)
            = ‖E4Fun z - E2Fun z ^ 2‖ * (‖phi8 τ‖ * ‖jInvariantFun τ‖) := by ring
          _ ≤ (Cσ * ‖qParamFun z‖) * (CΦ * (1 + ‖(τ : ℂ)‖) * Cjτ) :=
              mul_le_mul (hσz z hz) hjprod (by positivity) (by positivity)
          _ = Cσ * Cjτ * (CΦ * (1 + ‖(τ : ℂ)‖)) * ‖qParamFun z‖ := by ring
      have hjzsl : ‖288 - jInvariantFun z * (E4Fun z - E2Fun z ^ 2)‖ ≤ Cj * ‖qParamFun z‖ := by
        rw [show (288 : ℂ) - jInvariantFun z * (E4Fun z - E2Fun z ^ 2)
            = -(jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288) by ring, norm_neg]
        exact hjzs z hz
      have h2 : ‖phi8 τ * (288 - jInvariantFun z * (E4Fun z - E2Fun z ^ 2))‖
          ≤ Cj * (CΦ * (1 + ‖(τ : ℂ)‖)) * ‖qParamFun z‖ := by
        rw [norm_mul]
        calc ‖phi8 τ‖ * ‖288 - jInvariantFun z * (E4Fun z - E2Fun z ^ 2)‖
            ≤ (CΦ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) * (Cj * ‖qParamFun z‖) :=
              mul_le_mul (hΦ τ hτ) hjzsl (norm_nonneg _) (by positivity)
          _ ≤ (CΦ * (1 + ‖(τ : ℂ)‖)) * (Cj * ‖qParamFun z‖) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc CΦ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖
                  ≤ CΦ * (1 + ‖(τ : ℂ)‖) * 1 :=
                    mul_le_mul_of_nonneg_left hq1τ (by positivity)
                _ = CΦ * (1 + ‖(τ : ℂ)‖) := by ring
          _ = Cj * (CΦ * (1 + ‖(τ : ℂ)‖)) * ‖qParamFun z‖ := by ring
      calc ‖phi8 τ * ((E4Fun z - E2Fun z ^ 2) * jInvariantFun τ)
            + phi8 τ * (288 - jInvariantFun z * (E4Fun z - E2Fun z ^ 2))‖
          ≤ ‖phi8 τ * ((E4Fun z - E2Fun z ^ 2) * jInvariantFun τ)‖
            + ‖phi8 τ * (288 - jInvariantFun z * (E4Fun z - E2Fun z ^ 2))‖ := norm_add_le _ _
        _ ≤ Cσ * Cjτ * (CΦ * (1 + ‖(τ : ℂ)‖)) * ‖qParamFun z‖
            + Cj * (CΦ * (1 + ‖(τ : ℂ)‖)) * ‖qParamFun z‖ := add_le_add h1 h2
        _ = (Cσ * Cjτ + Cj) * (CΦ * (1 + ‖(τ : ℂ)‖)) * ‖qParamFun z‖ := by ring
    calc ‖(6 : ℂ) * E4Fun τ‖
          * ‖phi8 τ * ((E4Fun z - E2Fun z ^ 2) * jInvariantFun τ)
              + phi8 τ * (288 - jInvariantFun z * (E4Fun z - E2Fun z ^ 2))‖
        ≤ (6 * C4τ) * ((Cσ * Cjτ + Cj) * (CΦ * (1 + ‖(τ : ℂ)‖)) * ‖qParamFun z‖) :=
          mul_le_mul h6 hbracket (norm_nonneg _) (by positivity)
      _ = 6 * C4τ * CΦ * (Cσ * Cjτ + Cj) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  have hC24 : ‖1728 * phi0 τ * E4Fun τ ^ 3
        * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))‖
      ≤ 1728 * (C2τ + 3) * C4τ ^ 3 * (5 * Cσ + 2 * Cq2) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    have hφ0' : ‖(1728 : ℂ) * phi0 τ‖ ≤ 1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hφ0 (by norm_num)
    have h4 : ‖E4Fun τ ^ 3‖ ≤ C4τ ^ 3 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hE4τ τ hτ) 3
    have h5 : ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖
        ≤ (5 * Cσ + 2 * Cq2) * ‖qParamFun z‖ := by
      have h1 : ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2)‖ ≤ 5 * (Cσ * ‖qParamFun z‖) := by
        rw [norm_mul, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left (hσz z hz) (by norm_num)
      have h2 : ‖(2 : ℂ) * (E2Fun z ^ 2 - 1)‖ ≤ 2 * (Cq2 * ‖qParamFun z‖) := by
        rw [norm_mul, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left (hE2sq z hz) (by norm_num)
      calc ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖
          ≤ ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2)‖ + ‖(2 : ℂ) * (E2Fun z ^ 2 - 1)‖ := norm_sub_le _ _
        _ ≤ 5 * (Cσ * ‖qParamFun z‖) + 2 * (Cq2 * ‖qParamFun z‖) := add_le_add h1 h2
        _ = (5 * Cσ + 2 * Cq2) * ‖qParamFun z‖ := by ring
    have hmain : ‖1728 * phi0 τ * E4Fun τ ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))‖
        = ‖(1728 : ℂ) * phi0 τ‖ * ‖E4Fun τ ^ 3‖
          * ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖ := by
      rw [show (1728 : ℂ) * phi0 τ * E4Fun τ ^ 3
            * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))
          = ((1728 : ℂ) * phi0 τ) * E4Fun τ ^ 3
            * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)) by ring, norm_mul, norm_mul]
    rw [hmain]
    calc ‖(1728 : ℂ) * phi0 τ‖ * ‖E4Fun τ ^ 3‖
          * ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖
        ≤ (1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖))) * C4τ ^ 3
            * ((5 * Cσ + 2 * Cq2) * ‖qParamFun z‖) :=
          mul_le_mul (mul_le_mul hφ0' h4 (norm_nonneg _) (by positivity)) h5
            (norm_nonneg _) (by positivity)
      _ = 1728 * (C2τ + 3) * C4τ ^ 3 * (5 * Cσ + 2 * Cq2) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
          ring_nf
  have hD24 : ‖1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)‖
      ≤ 1728 * C4τ ^ 2 * C6τ * Cq2 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    have h4 : ‖E4Fun τ ^ 2‖ ≤ C4τ * C4τ := by
      rw [norm_pow, pow_two]
      exact mul_le_mul (hE4τ τ hτ) (hE4τ τ hτ) (norm_nonneg _) hC4τ.le
    have hmain : ‖1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)‖
        = ‖(1728 : ℂ)‖ * ‖(τ : ℂ)‖ * ‖E4Fun τ ^ 2‖ * ‖E6Fun τ‖ * ‖E2Fun z ^ 2 - 1‖ := by
      rw [show (1728 : ℂ) * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)
          = ((1728 : ℂ) * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ) * (E2Fun z ^ 2 - 1) by ring,
        norm_mul, norm_mul, norm_mul, norm_mul]
    rw [hmain]
    calc ‖(1728 : ℂ)‖ * ‖(τ : ℂ)‖ * ‖E4Fun τ ^ 2‖ * ‖E6Fun τ‖ * ‖E2Fun z ^ 2 - 1‖
        ≤ 1728 * (1 + ‖(τ : ℂ)‖) * (C4τ * C4τ) * C6τ * (Cq2 * ‖qParamFun z‖) := by
          have h1 : ‖(1728 : ℂ)‖ * ‖(τ : ℂ)‖ ≤ 1728 * (1 + ‖(τ : ℂ)‖) := by
            rw [Complex.norm_ofNat]
            nlinarith [ht0]
          exact mul_le_mul (mul_le_mul (mul_le_mul h1 h4 (norm_nonneg _) (by positivity))
            (hE6τ τ hτ) (norm_nonneg _) (by positivity)) (hE2sq z hz) (norm_nonneg _) (by positivity)
      _ = 1728 * C4τ ^ 2 * C6τ * Cq2 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring_nf
  have hφ2' : ‖(1728 : ℂ) * phi2 τ‖ ≤ 1728 * ((C2τ ^ 2 + 6 * C2τ) * (1 + ‖(τ : ℂ)‖)) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hφ2 (by norm_num)
  have h5term : ‖1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)‖
      ≤ 1728 * (C2τ ^ 2 + 6 * C2τ) * C4τ * C6τ * Cq4 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    have hmain : ‖1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)‖
        = ‖(1728 : ℂ) * phi2 τ‖ * ‖E4Fun τ‖ * ‖E6Fun τ‖ * ‖E4Fun z - 1‖ := by
      rw [show (1728 : ℂ) * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)
          = (((1728 : ℂ) * phi2 τ) * E4Fun τ * E6Fun τ) * (E4Fun z - 1) by ring,
        norm_mul, norm_mul, norm_mul]
    rw [hmain]
    calc ‖(1728 : ℂ) * phi2 τ‖ * ‖E4Fun τ‖ * ‖E6Fun τ‖ * ‖E4Fun z - 1‖
        ≤ (1728 * ((C2τ ^ 2 + 6 * C2τ) * (1 + ‖(τ : ℂ)‖))) * C4τ * C6τ
            * (Cq4 * ‖qParamFun z‖) :=
          mul_le_mul (mul_le_mul (mul_le_mul hφ2' (hE4τ τ hτ) (norm_nonneg _) (by positivity))
            (hE6τ τ hτ) (norm_nonneg _) (by positivity)) (hE4m1 z hz) (norm_nonneg _) (by positivity)
      _ = 1728 * (C2τ ^ 2 + 6 * C2τ) * C4τ * C6τ * Cq4 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
          ring_nf
  have hE24 : ‖1728 * phi0 τ * DeltaFun τ
        * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
        * E4Fun z ^ 2 / DeltaFun z‖
      ≤ 1728 * (C2τ + 3) * (CΔu + CΔu') * CR * B4 ^ 2 / cΔ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    have h4 : ‖E4Fun z ^ 2‖ ≤ B4 * B4 := by
      rw [norm_pow, pow_two]
      exact mul_le_mul (hE4z z hz) (hE4z z hz) (norm_nonneg _) hB4.le
    have hnum : ‖1728 * phi0 τ * DeltaFun τ
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2‖
        ≤ 1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) * ((CΔu + CΔu') * ‖qParamFun τ‖)
          * (CR * ‖qParamFun z‖ ^ 2) * (B4 * B4) := by
      have hφ0' : ‖(1728 : ℂ) * phi0 τ‖ ≤ 1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) := by
        rw [norm_mul, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left hφ0 (by norm_num)
      have hmain : ‖1728 * phi0 τ * DeltaFun τ
            * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
            * E4Fun z ^ 2‖
          = ‖(1728 : ℂ) * phi0 τ‖ * ‖DeltaFun τ‖
            * ‖5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z‖
            * ‖E4Fun z ^ 2‖ := by
        rw [show (1728 : ℂ) * phi0 τ * DeltaFun τ
              * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
              * E4Fun z ^ 2
            = (((1728 : ℂ) * phi0 τ * DeltaFun τ)
              * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z))
              * E4Fun z ^ 2 by ring, norm_mul, norm_mul, norm_mul]
      rw [hmain]
      calc ‖(1728 : ℂ) * phi0 τ‖ * ‖DeltaFun τ‖
            * ‖5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z‖
            * ‖E4Fun z ^ 2‖
          ≤ (1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) * ((CΔu + CΔu') * ‖qParamFun τ‖))
            * (CR * ‖qParamFun z‖ ^ 2) * (B4 * B4) :=
            mul_le_mul (mul_le_mul (mul_le_mul hφ0' hΔτu (norm_nonneg _) (by positivity))
              (hRz z hz) (norm_nonneg _) (by positivity)) h4 (norm_nonneg _) (by positivity)
        _ = 1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) * ((CΔu + CΔu') * ‖qParamFun τ‖)
            * (CR * ‖qParamFun z‖ ^ 2) * (B4 * B4) := rfl
    have hinv : ‖(DeltaFun z)⁻¹‖ ≤ (cΔ * ‖qParamFun z‖)⁻¹ := by
      rw [norm_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le (mul_pos hcΔ hDzpos) (hDzl z hz))
        (mul_pos hcΔ hDzpos)).mpr (hDzl z hz)
    have hdiv : ‖1728 * phi0 τ * DeltaFun τ
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2 / DeltaFun z‖
        = ‖1728 * phi0 τ * DeltaFun τ
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2‖ * ‖(DeltaFun z)⁻¹‖ := by
      rw [div_eq_mul_inv, norm_mul]
    rw [hdiv]
    calc ‖1728 * phi0 τ * DeltaFun τ
            * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
            * E4Fun z ^ 2‖ * ‖(DeltaFun z)⁻¹‖
        ≤ (1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) * ((CΔu + CΔu') * ‖qParamFun τ‖)
            * (CR * ‖qParamFun z‖ ^ 2) * (B4 * B4)) * (cΔ * ‖qParamFun z‖)⁻¹ :=
          mul_le_mul hnum hinv (norm_nonneg _) (by positivity)
      _ ≤ 1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) * ((CΔu + CΔu') * 1)
            * (CR * ‖qParamFun z‖ ^ 2) * (B4 * B4) * (cΔ * ‖qParamFun z‖)⁻¹ := by
          have h1 : ‖qParamFun τ‖ ≤ 1 := hq1τ
          have h2 : (CΔu + CΔu') * ‖qParamFun τ‖ ≤ (CΔu + CΔu') * 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          have h3 : 1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) * ((CΔu + CΔu') * ‖qParamFun τ‖)
              * (CR * ‖qParamFun z‖ ^ 2) * (B4 * B4)
              ≤ 1728 * ((C2τ + 3) * (1 + ‖(τ : ℂ)‖)) * ((CΔu + CΔu') * 1)
                * (CR * ‖qParamFun z‖ ^ 2) * (B4 * B4) := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left h2 (by positivity)
              · positivity
            · positivity
          exact mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 1728 * (C2τ + 3) * (CΔu + CΔu') * CR * B4 ^ 2 / cΔ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
          field_simp
  -- assembly
  have htri : ‖6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
            * (jInvariantFun τ - jInvariantFun z)
          + 1728 * E4Fun τ * phi8 τ
          + 1728 * phi0 τ * E4Fun τ ^ 3
            * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))
          + 1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)
          + 1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)‖
      ≤ (6 * C4τ * CΦ * (Cσ * Cjτ + Cj) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
          + 1728 * (C2τ + 3) * C4τ ^ 3 * (5 * Cσ + 2 * Cq2) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖)
          + (1728 * C4τ ^ 2 * C6τ * Cq2 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
            + 1728 * (C2τ ^ 2 + 6 * C2τ) * C4τ * C6τ * Cq4 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖) := by
    have t1 := norm_add_le (6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
          * (jInvariantFun τ - jInvariantFun z) + 1728 * E4Fun τ * phi8 τ)
        (1728 * phi0 τ * E4Fun τ ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)))
    have t2 := norm_add_le ((6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
          * (jInvariantFun τ - jInvariantFun z) + 1728 * E4Fun τ * phi8 τ)
        + (1728 * phi0 τ * E4Fun τ ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))))
        (1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1))
    have t3 := norm_add_le (((6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
          * (jInvariantFun τ - jInvariantFun z) + 1728 * E4Fun τ * phi8 τ)
        + (1728 * phi0 τ * E4Fun τ ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))))
        + 1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1))
        (1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1))
    have hAB'' : ‖6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
          * (jInvariantFun τ - jInvariantFun z) + 1728 * E4Fun τ * phi8 τ‖
        ≤ 6 * C4τ * CΦ * (Cσ * Cjτ + Cj) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := hAB
    have hC24'' : ‖1728 * phi0 τ * E4Fun τ ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))‖
        ≤ 1728 * (C2τ + 3) * C4τ ^ 3 * (5 * Cσ + 2 * Cq2) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := hC24
    have hD24'' : ‖1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)‖
        ≤ 1728 * C4τ ^ 2 * C6τ * Cq2 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := hD24
    have h5term'' : ‖1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)‖
        ≤ 1728 * (C2τ ^ 2 + 6 * C2τ) * C4τ * C6τ * Cq4 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := h5term
    linarith [t1, t2, t3, hAB'', hC24'', hD24'', h5term'',
      norm_nonneg (6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
        * (jInvariantFun τ - jInvariantFun z) + 1728 * E4Fun τ * phi8 τ),
      norm_nonneg (1728 * phi0 τ * E4Fun τ ^ 3
        * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))),
      norm_nonneg (1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)),
      norm_nonneg (1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1))]
  calc ‖6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
            * (jInvariantFun τ - jInvariantFun z)
          + 1728 * E4Fun τ * phi8 τ
          + 1728 * phi0 τ * E4Fun τ ^ 3
            * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))
          + 1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)
          + 1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)
          - 1728 * phi0 τ * DeltaFun τ
            * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
            * E4Fun z ^ 2 / DeltaFun z‖
      ≤ ‖6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
            * (jInvariantFun τ - jInvariantFun z)
          + 1728 * E4Fun τ * phi8 τ
          + 1728 * phi0 τ * E4Fun τ ^ 3
            * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))
          + 1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)
          + 1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)‖
        + ‖1728 * phi0 τ * DeltaFun τ
            * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
            * E4Fun z ^ 2 / DeltaFun z‖ := norm_sub_le _ _
    _ ≤ ((6 * C4τ * CΦ * (Cσ * Cjτ + Cj) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
          + 1728 * (C2τ + 3) * C4τ ^ 3 * (5 * Cσ + 2 * Cq2) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖)
          + (1728 * C4τ ^ 2 * C6τ * Cq2 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
            + 1728 * (C2τ ^ 2 + 6 * C2τ) * C4τ * C6τ * Cq4 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖))
        + 1728 * (C2τ + 3) * (CΔu + CΔu') * CR * B4 ^ 2 / cΔ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ :=
        add_le_add htri hE24
    _ = (6 * C4τ * CΦ * (Cσ * Cjτ + Cj) + 1728 * (C2τ + 3) * C4τ ^ 3 * (5 * Cσ + 2 * Cq2)
          + 1728 * C4τ ^ 2 * C6τ * Cq2 + 1728 * (C2τ ^ 2 + 6 * C2τ) * C4τ * C6τ * Cq4
          + 1728 * (C2τ + 3) * (CΔu + CΔu') * CR * B4 ^ 2 / cΔ)
          * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring

end

end Work.Asymptotics
