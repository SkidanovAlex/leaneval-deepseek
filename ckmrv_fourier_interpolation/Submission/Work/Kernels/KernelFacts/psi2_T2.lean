import Mathlib
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelSlash
import Submission.Work.Kernels.LogLambda.ThetaLaws

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelFacts

/-! ## The `T`-transformation laws of `U`, `V`, `W`, `ξ₂` -/

lemma T_smul_eq_vadd_one' (τ : ℍ) : ModularGroup.T • τ = (1:ℝ)+ᵥτ := by
  simpa using UpperHalfPlane.modular_T_zpow_smul τ (1:ℤ)

lemma UFun_vadd_one (τ : ℍ) : UFun ((1:ℝ)+ᵥτ) = WFun τ := by
  rw [← T_smul_eq_vadd_one' τ]
  simp only [UFun, WFun]
  rw [theta00Fun_T]

lemma WFun_vadd_one (τ : ℍ) : WFun ((1:ℝ)+ᵥτ) = UFun τ := by
  rw [← T_smul_eq_vadd_one' τ]
  simp only [UFun, WFun]
  rw [theta01Fun_T]

lemma VFun_vadd_one (τ : ℍ) : VFun ((1:ℝ)+ᵥτ) = - VFun τ := by
  rw [← T_smul_eq_vadd_one' τ]
  simp only [VFun]
  rw [theta10Fun_T, mul_pow]
  have hexp4 : (Complex.exp (Real.pi * Complex.I / 4)) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul]
    have h : ((4:ℕ):ℂ) * (Real.pi * Complex.I / 4) = Real.pi * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_pi_mul_I]
  rw [hexp4]
  ring

lemma xi2Fun_vadd_one (τ : ℍ) : xi2Fun ((1:ℝ)+ᵥτ) = xi2Fun τ := by
  simp only [xi2Fun, UFun_vadd_one, WFun_vadd_one]
  ring

lemma UFun_vadd_two (τ : ℍ) : UFun ((2:ℝ)+ᵥτ) = UFun τ := by
  rw [vadd_one_add_one, UFun_vadd_one, WFun_vadd_one]

lemma VFun_vadd_two (τ : ℍ) : VFun ((2:ℝ)+ᵥτ) = VFun τ := by
  rw [vadd_one_add_one, VFun_vadd_one, VFun_vadd_one, neg_neg]

lemma xi2Fun_vadd_two (τ : ℍ) : xi2Fun ((2:ℝ)+ᵥτ) = xi2Fun τ := by
  rw [vadd_one_add_one, xi2Fun_vadd_one, xi2Fun_vadd_one]

/-! ## The `S`-transformation laws of `U`, `V`, `W` and of `ξ₂` -/

lemma UFun_S_smul (τ : ℍ) : UFun (ModularGroup.S • τ) = - (τ:ℂ)^2 * UFun τ := by
  simp only [UFun]
  rw [theta00Fun_S, mul_pow]
  have hpow : ((-Complex.I * (τ:ℂ))^(1/2:ℂ))^4 = - (τ:ℂ)^2 := by
    rw [← Complex.cpow_nat_mul]
    have hexp : ((4:ℕ):ℂ) * (1/2:ℂ) = ((2:ℕ):ℂ) := by norm_num
    rw [hexp, Complex.cpow_natCast, mul_pow]
    rw [show (-Complex.I : ℂ)^2 = -1 by rw [pow_two, neg_mul_neg, Complex.I_mul_I]]
    ring
  rw [hpow]

lemma WFun_S_smul (τ : ℍ) : WFun (ModularGroup.S • τ) = - (τ:ℂ)^2 * VFun τ := by
  simp only [WFun, VFun]
  rw [theta01Fun_S, mul_pow]
  have hpow : ((-Complex.I * (τ:ℂ))^(1/2:ℂ))^4 = - (τ:ℂ)^2 := by
    rw [← Complex.cpow_nat_mul]
    have hexp : ((4:ℕ):ℂ) * (1/2:ℂ) = ((2:ℕ):ℂ) := by norm_num
    rw [hexp, Complex.cpow_natCast, mul_pow]
    rw [show (-Complex.I : ℂ)^2 = -1 by rw [pow_two, neg_mul_neg, Complex.I_mul_I]]
    ring
  rw [hpow]

lemma zpow_neg_two (z : ℂ) : z ^ (-2:ℤ) = (z^2)⁻¹ := by
  rw [show (-2:ℤ) = -(2:ℤ) from rfl, _root_.zpow_neg]
  simp

lemma UFun_slash_S (τ : ℍ) : (UFun ∣[(2:ℤ)] ModularGroup.S) τ = - UFun τ := by
  rw [slash_S_apply, UFun_S_smul, zpow_neg_two]
  have hτ : (τ:ℂ) ≠ 0 := coe_tau_ne_zero τ
  field_simp

lemma WFun_slash_S (τ : ℍ) : (WFun ∣[(2:ℤ)] ModularGroup.S) τ = - VFun τ := by
  rw [slash_S_apply, WFun_S_smul, zpow_neg_two]
  have hτ : (τ:ℂ) ≠ 0 := coe_tau_ne_zero τ
  field_simp

lemma xi2Fun_slash_S (τ : ℍ) : (xi2Fun ∣[(2:ℤ)] ModularGroup.S) τ = -(UFun τ + VFun τ) := by
  have hsplit : xi2Fun = UFun + WFun := rfl
  rw [hsplit, SlashAction.add_slash, Pi.add_apply, UFun_slash_S, WFun_slash_S]
  ring

/-! ## The transformation laws of `𝓛`, `𝓛_S` -/

lemma L_vadd_one (ℓ : LogLambdaData) (τ : ℍ) :
    ℓ.L ((1:ℝ)+ᵥτ) = ℓ.L τ - ℓ.L_S τ + (Real.pi:ℂ) * Complex.I := by
  have h := ℓ.slash_T τ
  rwa [slash_T_apply] at h

lemma L_S_vadd_one (ℓ : LogLambdaData) (τ : ℍ) :
    ℓ.L_S ((1:ℝ)+ᵥτ) = - ℓ.L_S τ := by
  have h := ℓ.slash_T_S τ
  rwa [slash_T_apply] at h

lemma L_vadd_two (ℓ : LogLambdaData) (τ : ℍ) :
    ℓ.L ((2:ℝ)+ᵥτ) = ℓ.L τ + 2 * ((Real.pi:ℂ) * Complex.I) := by
  rw [vadd_one_add_one, L_vadd_one ℓ ((1:ℝ)+ᵥτ), L_vadd_one ℓ τ, L_S_vadd_one ℓ τ]
  ring

lemma L_S_vadd_two (ℓ : LogLambdaData) (τ : ℍ) :
    ℓ.L_S ((2:ℝ)+ᵥτ) = ℓ.L_S τ := by
  rw [vadd_one_add_one, L_S_vadd_one ℓ ((1:ℝ)+ᵥτ), L_S_vadd_one ℓ τ, neg_neg]

/-! ## The main result -/

theorem psi2_T2 (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.T2op (Work.Kernels.psi2 ℓ) = 0 := by
  ext τ
  have hL1 := L_vadd_one ℓ τ
  have hLs1 := L_S_vadd_one ℓ τ
  have hL2 := L_vadd_two ℓ τ
  have hLs2 := L_S_vadd_two ℓ τ
  have hxi1 := xi2Fun_vadd_one τ
  have hxi2 := xi2Fun_vadd_two τ
  have hb0 := xi2Fun_slash_S τ
  have hb1 : (xi2Fun ∣[(2:ℤ)] ModularGroup.S) ((1:ℝ)+ᵥτ) = VFun τ - WFun τ := by
    rw [xi2Fun_slash_S, UFun_vadd_one, VFun_vadd_one]
    ring
  have hb2 : (xi2Fun ∣[(2:ℤ)] ModularGroup.S) ((2:ℝ)+ᵥτ) = -(UFun τ + VFun τ) := by
    rw [xi2Fun_slash_S, UFun_vadd_two, VFun_vadd_two]
  simp only [T2op, psi2, Pi.zero_apply]
  rw [hL2, hLs2, hxi2, hb2, hL1, hLs1, hxi1, hb1, hb0]
  simp only [xi2Fun]
  ring

end Work.Kernels.KernelFacts
