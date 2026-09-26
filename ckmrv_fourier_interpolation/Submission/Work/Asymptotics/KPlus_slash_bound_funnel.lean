import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlus_slash_cusp_ball
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Asymptotics.ZAtomsThird.first_order
import Submission.Work.Asymptotics.ZAtomsThird.cusp_forms
import Submission.Work.Asymptotics.KPlusFunnel.Atoms
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.KPlusFunnel.Bounds

set_option maxHeartbeats 4000000

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm

noncomputable section

open Work.Kernels

/-! ## Glue: the `z`-estimates at the threshold `1/3` -/

/-- `‖E₄(z)‖` is bounded on `{Im z ≥ 1/3}`. -/
theorem E4_bounded_third :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z‖ ≤ B := by
  obtain ⟨C, hC, h⟩ := ZAtomsThird.E4Fun_two_term_third
  refine ⟨1 + 80 + C / 9 + 1, by positivity, fun z hz => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq3 : ‖qParamFun z‖ ≤ 1 / 3 := norm_qParam_le_third hz
  have h1 := h z hz
  have hsplit : E4Fun z = (E4Fun z - 1 - 240 * qParamFun z) + 1 + 240 * qParamFun z := by ring
  rw [hsplit]
  have h240 : ‖(240 : ℂ) * qParamFun z‖ = 240 * ‖qParamFun z‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  calc ‖(E4Fun z - 1 - 240 * qParamFun z) + 1 + 240 * qParamFun z‖
      ≤ (‖E4Fun z - 1 - 240 * qParamFun z‖ + 1) + ‖(240 : ℂ) * qParamFun z‖ := by
        have s := norm_add_le ((E4Fun z - 1 - 240 * qParamFun z) + 1) (240 * qParamFun z)
        have t : ‖(E4Fun z - 1 - 240 * qParamFun z) + 1‖
            ≤ ‖E4Fun z - 1 - 240 * qParamFun z‖ + 1 := by
          have := norm_add_le (E4Fun z - 1 - 240 * qParamFun z) (1 : ℂ)
          rw [norm_one] at this
          exact this
        linarith [s, t, norm_nonneg ((E4Fun z - 1 - 240 * qParamFun z) + 1)]
    _ ≤ (C * ‖qParamFun z‖ ^ 2 + 1) + 240 * ‖qParamFun z‖ := by
        rw [h240]
        linarith [h1, norm_nonneg (E4Fun z - 1 - 240 * qParamFun z)]
    _ ≤ 1 + 80 + C / 9 + 1 := by
        have hq2 : ‖qParamFun z‖ ^ 2 ≤ 1 / 9 := by nlinarith
        nlinarith [hC.le, hq0, hq2, hq3]
    _ ≤ 1 + 80 + C / 9 + 1 := le_rfl

/-- `E₂(z)² - 1 = O(q(z))` on `{Im z ≥ 1/3}`. -/
theorem E2sq_sub_one_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E2Fun z ^ 2 - 1‖ ≤ C * ‖qParamFun z‖ := by
  obtain ⟨C, hC, h⟩ := ZAtomsThird.E2Fun_two_term_third
  refine ⟨(24 + C / 3) * (24 + C / 3 + 2) + 1, by positivity, fun z hz => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := le_trans (norm_qParam_le_third hz) (by norm_num)
  have h1 := h z hz
  have hE2m1 : ‖E2Fun z - 1‖ ≤ (24 + C / 3) * ‖qParamFun z‖ := by
    have hsplit : E2Fun z - 1 = (E2Fun z - 1 + 24 * qParamFun z) - 24 * qParamFun z := by ring
    rw [hsplit]
    have h24 : ‖(24 : ℂ) * qParamFun z‖ = 24 * ‖qParamFun z‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    calc ‖(E2Fun z - 1 + 24 * qParamFun z) - 24 * qParamFun z‖
        ≤ ‖E2Fun z - 1 + 24 * qParamFun z‖ + ‖(24 : ℂ) * qParamFun z‖ := norm_sub_le _ _
      _ ≤ C * ‖qParamFun z‖ ^ 2 + 24 * ‖qParamFun z‖ := by rw [h24]; linarith
      _ ≤ (24 + C / 3) * ‖qParamFun z‖ := by
          have hq3 : ‖qParamFun z‖ ≤ 1 / 3 := norm_qParam_le_third hz
          have : C * ‖qParamFun z‖ ^ 2 ≤ C / 3 * ‖qParamFun z‖ := by
            have h2 : ‖qParamFun z‖ ^ 2 ≤ (1 / 3) * ‖qParamFun z‖ := by nlinarith
            nlinarith [hC.le, h2, hq0]
          linarith
  have hE2p1 : ‖E2Fun z + 1‖ ≤ 24 + C / 3 + 2 := by
    have : E2Fun z + 1 = (E2Fun z - 1) + 2 := by ring
    rw [this]
    calc ‖(E2Fun z - 1) + 2‖ ≤ ‖E2Fun z - 1‖ + 2 := by
          have := norm_add_le (E2Fun z - 1) (2 : ℂ)
          rw [Complex.norm_ofNat] at this
          exact this
      _ ≤ (24 + C / 3) * ‖qParamFun z‖ + 2 := by linarith
      _ ≤ 24 + C / 3 + 2 := by
          have : (24 + C / 3) * ‖qParamFun z‖ ≤ 24 + C / 3 :=
            mul_le_of_le_one_right (by positivity) hq1
          linarith
  have hsplit : E2Fun z ^ 2 - 1 = (E2Fun z - 1) * (E2Fun z + 1) := by ring
  rw [hsplit, norm_mul]
  calc ‖E2Fun z - 1‖ * ‖E2Fun z + 1‖
      ≤ ((24 + C / 3) * ‖qParamFun z‖) * (24 + C / 3 + 2) :=
        mul_le_mul hE2m1 hE2p1 (norm_nonneg _) (by positivity)
    _ ≤ ((24 + C / 3) * (24 + C / 3 + 2) + 1) * ‖qParamFun z‖ := by
        nlinarith [hq0, hq1, hC.le]

/-- `E₄(z) - 1 = O(q(z))` on `{Im z ≥ 1/3}`. -/
theorem E4_sub_one_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z - 1‖ ≤ C * ‖qParamFun z‖ := by
  obtain ⟨C, hC, h⟩ := ZAtomsThird.E4Fun_two_term_third
  refine ⟨240 + C / 3 + 1, by positivity, fun z hz => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq3 : ‖qParamFun z‖ ≤ 1 / 3 := norm_qParam_le_third hz
  have h1 := h z hz
  have hsplit : E4Fun z - 1 = (E4Fun z - 1 - 240 * qParamFun z) + 240 * qParamFun z := by ring
  rw [hsplit]
  have h240 : ‖(240 : ℂ) * qParamFun z‖ = 240 * ‖qParamFun z‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  calc ‖(E4Fun z - 1 - 240 * qParamFun z) + 240 * qParamFun z‖
      ≤ ‖E4Fun z - 1 - 240 * qParamFun z‖ + ‖(240 : ℂ) * qParamFun z‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun z‖ ^ 2 + 240 * ‖qParamFun z‖ := by rw [h240]; linarith
    _ ≤ (240 + C / 3 + 1) * ‖qParamFun z‖ := by
        have h2 : C * ‖qParamFun z‖ ^ 2 ≤ C / 3 * ‖qParamFun z‖ := by
          have h3 : ‖qParamFun z‖ ^ 2 ≤ (1 / 3) * ‖qParamFun z‖ := by nlinarith
          nlinarith [hC.le, h3, hq0]
        nlinarith [h2, hq0]

/-! ## The main theorem -/

theorem KPlus_slash_bound_funnel (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (τ z : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → 1 / 3 ≤ z.im →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ ((d : ℤ) / 2 - 2) * Work.Kernels.KPlus d τ (ModularGroup.S • z)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun z‖
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨Cσ, hCσ, hσ⟩ := ZAtomsThird.cusp_forms
  obtain ⟨cΔ, hcΔ, hΔl⟩ := delta_lower_third
  obtain ⟨CD, hCD, hΔu⟩ := delta_upper_third
  obtain ⟨B4, hB4, hE4⟩ := E4_bounded_third
  obtain ⟨Cq2, hCq2, hE2sq⟩ := E2sq_sub_one_third
  obtain ⟨Cq4, hCq4, hE4m1⟩ := E4_sub_one_third
  obtain ⟨Cj, hCj, hjzσ⟩ := jz_sigma_third
  have hσz : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cσ * ‖qParamFun z‖ :=
    fun z hz => hσ.1 z hz
  have hεz : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖E2Fun z * E6Fun z - E4Fun z ^ 2‖ ≤ Cσ * ‖qParamFun z‖ := fun z hz => hσ.2.1 z hz
  have hRz : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z‖
        ≤ Cσ * ‖qParamFun z‖ ^ 2 := fun z hz => hσ.2.2.2 z hz
  rcases hd with rfl | rfl
  · have hE4' : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z‖ ≤ B4 := hE4
    have hΔu' : ∀ z : ℍ, 1 / 3 ≤ z.im → ‖DeltaFun z‖ ≤ CD * ‖qParamFun z‖ := hΔu
    obtain ⟨C8, A8, hC8, hA8, hX⟩ :=
      Xi8_bound_funnel Cσ Cσ CD B4 hCσ hCσ hCD hB4 hσz hεz hE4' hΔu'
    have hpi : (Real.pi : ℂ) ^ (-2 : ℤ) ≠ 0 :=
      zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    have hcne : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
    refine ⟨C8 / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖, A8,
      div_pos hC8 (norm_pos_iff.mpr hcne), hA8, fun τ z hD hτ hz hne => ?_⟩
    have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr hne
    have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
    have hcD : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * (DeltaFun z * (jInvariantFun τ - jInvariantFun z)) ≠ 0 :=
      mul_ne_zero hcne (mul_ne_zero hDz hJ)
    have hkey := Xi8_eq τ z hne
    have hXi : (z : ℂ) ^ 2 * KPlus 8 τ (ModularGroup.S • z)
        = Xi8 τ z / ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
            * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))) := by
      rw [eq_div_iff hcD, mul_comm]
      exact hkey
    have hzpow : (z : ℂ) ^ (((8 : ℕ) : ℤ) / 2 - 2) = (z : ℂ) ^ 2 := by
      rw [show (((8 : ℕ) : ℤ) / 2 - 2) = (2 : ℤ) by norm_num, _root_.zpow_ofNat]
    rw [hzpow, hXi, norm_div, norm_mul]
    have hb := hX τ z ⟨hD, hτ⟩ hz
    have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
    have hden : (0 : ℝ) < ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖
        * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
      mul_pos (norm_pos_iff.mpr hcne) (norm_pos_iff.mpr (mul_ne_zero hDz hJ))
    calc ‖Xi8 τ z‖ / (‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖
            * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖)
        ≤ (C8 * (1 + ‖(τ : ℂ)‖) ^ A8 * ‖qParamFun z‖) / (‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖
            * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖) :=
          div_le_div_of_nonneg_right hb hden.le
      _ = C8 / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * (1 + ‖(τ : ℂ)‖) ^ A8
            * ‖qParamFun z‖ / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by ring
  · obtain ⟨C24, A24, hC24, hA24, hX⟩ :=
      Xi24_bound_funnel Cσ Cσ Cq2 Cq4 Cj cΔ CD B4 hCσ hCσ hCq2 hCq4 hCj hcΔ hCD hB4
        hσz hRz hE2sq hE4m1 hjzσ hE4 hΔl hΔu
    have hpi : (Real.pi : ℂ) ^ (-2 : ℤ) ≠ 0 :=
      zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    have hcne : (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by simp [Work.Kernels.c1728])) hpi)
        Complex.I_ne_zero
    refine ⟨C24 / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖, A24,
      div_pos hC24 (norm_pos_iff.mpr hcne), hA24, fun τ z hD hτ hz hne => ?_⟩
    have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr hne
    have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
    have hcD : (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * (DeltaFun z * (jInvariantFun τ - jInvariantFun z)) ≠ 0 :=
      mul_ne_zero hcne (mul_ne_zero hDz hJ)
    have hkey := Xi24_eq τ z hne
    have hXi : (z : ℂ) ^ 10 * KPlus 24 τ (ModularGroup.S • z)
        = Xi24 τ z / ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
            * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))) := by
      rw [eq_div_iff hcD, mul_comm]
      exact hkey
    have hzpow : (z : ℂ) ^ (((24 : ℕ) : ℤ) / 2 - 2) = (z : ℂ) ^ 10 := by
      rw [show (((24 : ℕ) : ℤ) / 2 - 2) = (10 : ℤ) by norm_num, _root_.zpow_ofNat]
    rw [hzpow, hXi, norm_div, norm_mul]
    have hb := hX τ z ⟨hD, hτ⟩ hz
    have hden : (0 : ℝ) < ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖
        * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
      mul_pos (norm_pos_iff.mpr hcne) (norm_pos_iff.mpr (mul_ne_zero hDz hJ))
    calc ‖Xi24 τ z‖ / (‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖
            * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖)
        ≤ (C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖qParamFun z‖) / (‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖
            * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖) :=
          div_le_div_of_nonneg_right hb hden.le
      _ = C24 / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * (1 + ‖(τ : ℂ)‖) ^ A24
            * ‖qParamFun z‖ / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by ring

end

end Work.Asymptotics
