/-
# Basic facts about the modular lambda function λ = θ₁₀⁴/θ₀₀⁴

This file collects the elementary transformation laws of
`U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴`, of `λ = V/U` and `λ_S = W/U`, together with the
holomorphy of `λ` and its nonvanishing.  These are the inputs to the fundamental-domain and
Hauptmodul developments below.
-/
import Mathlib
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Kernels.TildeFacts.theta_quartic

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

open Work.Kernels Work.Kernels.LogLambda

/-! ## Nonvanishing of the theta functions and of `U`, `V`, `W`, `λ`, `λ_S` -/

lemma UFun_ne_zero (τ : ℍ) : UFun τ ≠ 0 := by
  simp only [UFun]; exact pow_ne_zero 4 (theta00Fun_ne_zero τ)

lemma VFun_ne_zero (τ : ℍ) : VFun τ ≠ 0 := by
  simp only [VFun]; exact pow_ne_zero 4 (theta10Fun_ne_zero τ)

lemma WFun_ne_zero (τ : ℍ) : WFun τ ≠ 0 := by
  simp only [WFun]; exact pow_ne_zero 4 (theta01Fun_ne_zero τ)

lemma lambdaFun_ne_zero (τ : ℍ) : lambdaFun τ ≠ 0 :=
  div_ne_zero (VFun_ne_zero τ) (UFun_ne_zero τ)

lemma lambdaSFun_ne_zero (τ : ℍ) : lambdaSFun τ ≠ 0 :=
  div_ne_zero (WFun_ne_zero τ) (UFun_ne_zero τ)

/-! ## The transformation laws of `U`, `V`, `W` -/

lemma UFun_T (τ : ℍ) : UFun (ModularGroup.T • τ) = WFun τ := by
  simp only [UFun, WFun, theta00Fun_T]

lemma WFun_T (τ : ℍ) : WFun (ModularGroup.T • τ) = UFun τ := by
  simp only [UFun, WFun, theta01Fun_T]

lemma VFun_T (τ : ℍ) : VFun (ModularGroup.T • τ) = -VFun τ := by
  rw [VFun, theta10Fun_T, mul_pow]
  have h : (Complex.exp (Real.pi * Complex.I / 4)) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul]
    have : (4 : ℕ) * (Real.pi * Complex.I / 4) = Real.pi * Complex.I := by ring
    rw [this, Complex.exp_pi_mul_I]
  rw [h]
  ring

private lemma cpow_half_pow_four (τ : ℍ) :
    ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 = -((τ : ℂ) ^ 2) := by
  rw [← Complex.cpow_nat_mul]
  norm_num
  rw [mul_pow, Complex.I_sq]
  ring

lemma UFun_S (τ : ℍ) : UFun (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * UFun τ := by
  rw [UFun, theta00Fun_S, mul_pow, cpow_half_pow_four]

lemma WFun_S (τ : ℍ) : WFun (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * VFun τ := by
  rw [WFun, VFun, theta01Fun_S, mul_pow, cpow_half_pow_four]

lemma VFun_S (τ : ℍ) : VFun (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * WFun τ := by
  rw [VFun, WFun, theta10Fun_S, mul_pow, cpow_half_pow_four]

/-! ## The transformation laws of `λ` and `λ_S` -/

private lemma lambda_aux (x y : ℂ) (hy : y ≠ 0) : -((-x) / y) / y⁻¹ = x := by
  field_simp

lemma lambdaFun_T2 (τ : ℍ) : lambdaFun (ModularGroup.T ^ 2 • τ) = lambdaFun τ := by
  have hT : (ModularGroup.T ^ 2 : SL(2, ℤ)) • τ
      = ModularGroup.T • (ModularGroup.T • τ) := by
    rw [pow_two, mul_smul]
  rw [hT, lambdaFun_T, lambdaSFun_T, lambdaFun_T]
  exact lambda_aux (lambdaFun τ) (lambdaSFun τ) (lambdaSFun_ne_zero τ)

lemma lambdaSFun_T2 (τ : ℍ) : lambdaSFun (ModularGroup.T ^ 2 • τ) = lambdaSFun τ := by
  have hT : (ModularGroup.T ^ 2 : SL(2, ℤ)) • τ
      = ModularGroup.T • (ModularGroup.T • τ) := by
    rw [pow_two, mul_smul]
  rw [hT, lambdaSFun_T, lambdaSFun_T, inv_inv]

lemma lambdaSFun_T2_inv (τ : ℍ) :
    lambdaSFun ((ModularGroup.T ^ 2 : SL(2, ℤ))⁻¹ • τ) = lambdaSFun τ := by
  have h := lambdaSFun_T2 ((ModularGroup.T ^ 2 : SL(2, ℤ))⁻¹ • τ)
  rw [smul_inv_smul] at h
  exact h.symm

/-- `λ` is invariant under `M = [[1,0],[-2,1]] = -S T^{-2} S`. -/
lemma lambdaFun_M (τ : ℍ) :
    lambdaFun ((-(ModularGroup.S * (ModularGroup.T ^ 2)⁻¹ * ModularGroup.S)) • τ)
      = lambdaFun τ := by
  rw [ModularGroup.SL_neg_smul, mul_smul, mul_smul]
  rw [lambdaFun_S, lambdaSFun_T2_inv, lambdaSFun_S]

/-! ## The quartic identity `U = V + W` and its consequences -/

/-- `λ_S = 1 - λ`. -/
lemma lambdaFun_add_lambdaSFun (τ : ℍ) : lambdaFun τ + lambdaSFun τ = 1 := by
  have hq := Work.Kernels.TildeFacts.theta_quartic τ
  have hU : UFun τ ≠ 0 := UFun_ne_zero τ
  have h : VFun τ / UFun τ + WFun τ / UFun τ = 1 := by
    rw [← add_div, add_comm (VFun τ) (WFun τ), ← hq, div_self hU]
  simpa only [lambdaFun, lambdaSFun] using h

/-- `λ` avoids the value `1` on `ℍ`. -/
lemma lambdaFun_ne_one (τ : ℍ) : lambdaFun τ ≠ 1 := by
  intro h
  have h2 : lambdaSFun τ = 0 := by
    have h3 := lambdaFun_add_lambdaSFun τ
    rw [h] at h3
    have h5 : (1 : ℂ) + lambdaSFun τ - 1 = 0 := by rw [h3]; ring
    simpa [add_sub_cancel_left] using h5
  exact lambdaSFun_ne_zero τ h2

/-! ## Holomorphy -/

lemma mdifferentiable_lambdaFun : MDiff lambdaFun := by
  have hV : MDiff (fun τ : ℍ => Work.Kernels.theta10Fun τ) := Work.Modular.mdifferentiable_theta2
  have hU : MDiff (fun τ : ℍ => Work.Kernels.theta00Fun τ) := Work.Modular.mdifferentiable_theta3
  have h : MDiff (fun τ : ℍ => Work.Kernels.theta10Fun τ ^ 4
      / Work.Kernels.theta00Fun τ ^ 4) :=
    (hV.pow 4).div (hU.pow 4) (fun τ => pow_ne_zero 4 (theta00Fun_ne_zero τ))
  simpa only [lambdaFun, VFun, UFun] using h

end Work.Rigidity
