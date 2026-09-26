/-
# `ψ₄` is annihilated by `(T - I)²`

CKMRV Proposition 4.3: `ψ₄ = ξ₄·𝓛 + (ξ₄|₄S)·𝓛_S` lies in
`Ann_k(𝓘₋, 𝒫)`, i.e. `ψ₄ |_k (T-I)² = 0` and `ψ₄ |_k (S-I) = 0`.  This file proves the
first of these in the explicit pointwise form `T2op (ψ₄) = 0`, where
`T2op F (τ) = F(τ+2) - 2F(τ+1) + F(τ)`.

The point is that `ξ₄(τ) + (ξ₄|₄S)(τ) + (ξ₄|₄S)(τ+1) = 0`, which follows from the
transformation laws of the Jacobi theta functions `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴`
under `T` and `S` (CKMRV (2.11)).

## Main result

* `Work.Kernels.KernelFacts.psi4_T2`
-/
import Mathlib
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.Kernels
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.theta2_S_smul
import Submission.Work.Modular.theta4_S_smul

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelFacts

/-! ## Transformation laws of `U`, `V`, `W`

`U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴` are the weight-two modular forms for `Γ(2)`; under `T` and
`S` they transform by CKMRV (2.11):

  `U|₂T = W`, `V|₂T = -V`, `W|₂T = U`, `U|₂S = -U`, `V|₂S = -W`, `W|₂S = -V`.
-/

lemma UFun_T_smul (τ : ℍ) : UFun (ModularGroup.T • τ) = WFun τ := by
  have h := Work.Modular.theta3_T_smul τ
  simp only [UFun, theta00Fun, WFun, theta01Fun, Work.Modular.theta3,
    Work.Modular.theta4] at h ⊢
  rw [h]

lemma WFun_T_smul (τ : ℍ) : WFun (ModularGroup.T • τ) = UFun τ := by
  have h := Work.Modular.theta4_T_smul τ
  simp only [UFun, theta00Fun, WFun, theta01Fun, Work.Modular.theta3,
    Work.Modular.theta4] at h ⊢
  rw [h]

lemma VFun_T_smul (τ : ℍ) : VFun (ModularGroup.T • τ) = - VFun τ := by
  have h := Work.Modular.theta2_T_smul τ
  simp only [VFun, theta10Fun, Work.Modular.theta2] at h ⊢
  rw [h, mul_pow]
  rw [show Complex.exp (↑Real.pi * Complex.I / 4) ^ 4 = -1 from by
    rw [← Complex.exp_nat_mul]
    rw [show ((4:ℕ):ℂ) * (↑Real.pi * Complex.I / 4) = ↑Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I]
  ring

lemma UFun_S_smul (τ : ℍ) : UFun (ModularGroup.S • τ) = -((τ : ℂ) ^ 2) * UFun τ := by
  have h := Work.Modular.theta3_S_smul τ
  simp only [UFun, theta00Fun, Work.Modular.theta3] at h ⊢
  rw [h, mul_pow]
  have hpow : ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 = -((τ : ℂ) ^ 2) := by
    rw [← Complex.cpow_nat_mul]
    rw [show ((4:ℕ):ℂ) * (1 / 2 : ℂ) = ((2:ℕ):ℂ) by norm_num, Complex.cpow_natCast]
    rw [mul_pow, neg_sq, Complex.I_sq]; ring
  rw [hpow]

lemma WFun_S_smul (τ : ℍ) : WFun (ModularGroup.S • τ) = -((τ : ℂ) ^ 2) * VFun τ := by
  have h := Work.Modular.theta4_S_smul τ
  simp only [VFun, WFun, theta01Fun, theta10Fun, Work.Modular.theta2,
    Work.Modular.theta4] at h ⊢
  rw [h, mul_pow]
  have hpow : ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 = -((τ : ℂ) ^ 2) := by
    rw [← Complex.cpow_nat_mul]
    rw [show ((4:ℕ):ℂ) * (1 / 2 : ℂ) = ((2:ℕ):ℂ) by norm_num, Complex.cpow_natCast]
    rw [mul_pow, neg_sq, Complex.I_sq]; ring
  rw [hpow]

lemma VFun_S_smul (τ : ℍ) : VFun (ModularGroup.S • τ) = -((τ : ℂ) ^ 2) * WFun τ := by
  have h := Work.Modular.theta2_S_smul τ
  simp only [VFun, WFun, theta01Fun, theta10Fun, Work.Modular.theta2,
    Work.Modular.theta4] at h ⊢
  rw [h, mul_pow]
  have hpow : ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 = -((τ : ℂ) ^ 2) := by
    rw [← Complex.cpow_nat_mul]
    rw [show ((4:ℕ):ℂ) * (1 / 2 : ℂ) = ((2:ℕ):ℂ) by norm_num, Complex.cpow_natCast]
    rw [mul_pow, neg_sq, Complex.I_sq]; ring
  rw [hpow]

/-! ### The same laws at `τ + 1` and `τ + 2` -/

lemma UFun_vadd_one (τ : ℍ) : UFun ((1 : ℝ) +ᵥ τ) = WFun τ := by
  rw [← UpperHalfPlane.modular_T_smul τ]; exact UFun_T_smul τ

lemma WFun_vadd_one (τ : ℍ) : WFun ((1 : ℝ) +ᵥ τ) = UFun τ := by
  rw [← UpperHalfPlane.modular_T_smul τ]; exact WFun_T_smul τ

lemma VFun_vadd_one (τ : ℍ) : VFun ((1 : ℝ) +ᵥ τ) = - VFun τ := by
  rw [← UpperHalfPlane.modular_T_smul τ]; exact VFun_T_smul τ

lemma UFun_vadd_two (τ : ℍ) : UFun ((2 : ℝ) +ᵥ τ) = UFun τ := by
  rw [vadd_one_add_one, UFun_vadd_one, WFun_vadd_one]

lemma WFun_vadd_two (τ : ℍ) : WFun ((2 : ℝ) +ᵥ τ) = WFun τ := by
  rw [vadd_one_add_one, WFun_vadd_one, UFun_vadd_one]

lemma VFun_vadd_two (τ : ℍ) : VFun ((2 : ℝ) +ᵥ τ) = VFun τ := by
  rw [vadd_one_add_one, VFun_vadd_one, VFun_vadd_one]; ring

/-! ## `ξ₄ = U² + W² - 2V²` and its `S`-transform -/

lemma xi4Fun_vadd_one (τ : ℍ) : xi4Fun ((1 : ℝ) +ᵥ τ) = xi4Fun τ := by
  simp only [xi4Fun, UFun_vadd_one, WFun_vadd_one, VFun_vadd_one]; ring

/-- `(ξ₄|₄S)(τ) = U(τ)² + V(τ)² - 2W(τ)²`. -/
lemma xi4S_apply (τ : ℍ) :
    (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ = UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2 := by
  rw [Work.Kernels.slash_S_apply]
  simp only [xi4Fun]
  rw [UFun_S_smul, WFun_S_smul, VFun_S_smul]
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← UpperHalfPlane.coe_im τ, h]; simp)
  field_simp

/-- `(ξ₄|₄S)(τ+1) = W(τ)² + V(τ)² - 2U(τ)²`. -/
lemma xi4S_vadd_one (τ : ℍ) :
    (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) ((1 : ℝ) +ᵥ τ) =
      WFun τ ^ 2 + VFun τ ^ 2 - 2 * UFun τ ^ 2 := by
  rw [xi4S_apply ((1 : ℝ) +ᵥ τ)]
  simp only [UFun_vadd_one, WFun_vadd_one, VFun_vadd_one]
  ring

lemma xi4S_vadd_two (τ : ℍ) :
    (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) ((2 : ℝ) +ᵥ τ) =
      (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ := by
  rw [xi4S_apply ((2 : ℝ) +ᵥ τ), xi4S_apply τ]
  simp only [UFun_vadd_two, WFun_vadd_two, VFun_vadd_two]

/-! ## The transformation laws of `𝓛`, `𝓛_S` at `τ + 1`, `τ + 2` -/

lemma jFunT_eq_one (τ : ℍ) : Work.Kernels.jFun ModularGroup.T (τ : ℂ) = 1 := by
  rw [Work.Kernels.jFun_apply]
  have h0 : (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 = 0 := by decide
  have h1 : (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 = 1 := by decide
  rw [h0, h1]; norm_num

/-- `𝓛(τ+1) = 𝓛(τ) - 𝓛_S(τ) + πi`. -/
lemma LogL_vadd_one (ℓ : LogLambdaData) (τ : ℍ) :
    ℓ.L ((1 : ℝ) +ᵥ τ) = ℓ.L τ - ℓ.L_S τ + (Real.pi : ℂ) * Complex.I := by
  have h := ℓ.slash_T τ
  rw [Work.Kernels.slash_apply'] at h
  have hT : ModularGroup.T • τ = (1 : ℝ) +ᵥ τ := by
    simpa using UpperHalfPlane.modular_T_zpow_smul τ (1 : ℤ)
  rw [hT, jFunT_eq_one τ] at h
  simpa using h

/-- `𝓛_S(τ+1) = -𝓛_S(τ)`. -/
lemma LogLS_vadd_one (ℓ : LogLambdaData) (τ : ℍ) :
    ℓ.L_S ((1 : ℝ) +ᵥ τ) = - ℓ.L_S τ := by
  have h := ℓ.slash_T_S τ
  rw [Work.Kernels.slash_apply'] at h
  have hT : ModularGroup.T • τ = (1 : ℝ) +ᵥ τ := by
    simpa using UpperHalfPlane.modular_T_zpow_smul τ (1 : ℤ)
  rw [hT, jFunT_eq_one τ] at h
  simpa using h

/-- `𝓛(τ+2) = 𝓛(τ) + 2πi`. -/
lemma LogL_vadd_two (ℓ : LogLambdaData) (τ : ℍ) :
    ℓ.L ((2 : ℝ) +ᵥ τ) = ℓ.L τ + 2 * ((Real.pi : ℂ) * Complex.I) := by
  rw [vadd_one_add_one, LogL_vadd_one ℓ, LogLS_vadd_one ℓ, LogL_vadd_one ℓ]; ring

/-- `𝓛_S(τ+2) = 𝓛_S(τ)`. -/
lemma LogLS_vadd_two (ℓ : LogLambdaData) (τ : ℍ) :
    ℓ.L_S ((2 : ℝ) +ᵥ τ) = ℓ.L_S τ := by
  rw [vadd_one_add_one, LogLS_vadd_one ℓ, LogLS_vadd_one ℓ]; ring

/-! ## The action of `(T-I)²` on the two summands of `ψ₄` -/

lemma T2op_fun_add (F G : ℍ → ℂ) : T2op (F + G) = T2op F + T2op G := by
  ext τ; simp only [T2op, Pi.add_apply]; ring

/-- If `F` is `T`-periodic then `(T-I)²(FG) = F·(T-I)²G`. -/
lemma T2op_mul_periodic {F G : ℍ → ℂ} (hF : ∀ τ, F ((1 : ℝ) +ᵥ τ) = F τ) :
    T2op (fun τ => F τ * G τ) = fun τ => F τ * T2op G τ := by
  ext τ
  have h2 : F ((2 : ℝ) +ᵥ τ) = F τ := by rw [vadd_one_add_one, hF, hF]
  simp only [T2op]
  rw [h2, hF τ]; ring

/-- `(T-I)²𝓛 = 2𝓛_S`. -/
lemma T2op_LogL (ℓ : LogLambdaData) : T2op ℓ.L = fun τ => 2 * ℓ.L_S τ := by
  ext τ; simp only [T2op]; rw [LogL_vadd_two ℓ τ, LogL_vadd_one ℓ τ]; ring

/-- `(T-I)²((ξ₄|₄S)·𝓛_S) = 2𝓛_S·((ξ₄|₄S) + (ξ₄|₄S)(·+1))`. -/
lemma T2op_xi4S_LogLS (ℓ : LogLambdaData) :
    T2op (fun τ => (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ)
      = fun τ => 2 * ℓ.L_S τ * ((xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ
          + (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) ((1 : ℝ) +ᵥ τ)) := by
  ext τ; simp only [T2op]
  rw [xi4S_vadd_two τ, LogLS_vadd_two ℓ τ, LogLS_vadd_one ℓ τ]; ring

/-! ## The main result -/

/-- `ψ₄` is annihilated by `(T-I)²` (CKMRV Proposition 4.3). -/
theorem psi4_T2 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Kernels.T2op (Work.Kernels.psi4 ℓ) = 0 := by
  have hpsi : Work.Kernels.psi4 ℓ
      = (fun τ : ℍ => Work.Kernels.xi4Fun τ * ℓ.L τ)
        + (fun τ : ℍ => (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ) := rfl
  rw [hpsi, T2op_fun_add, T2op_mul_periodic xi4Fun_vadd_one, T2op_LogL, T2op_xi4S_LogLS]
  ext τ
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [xi4S_apply τ, xi4S_vadd_one τ]
  simp only [Work.Kernels.xi4Fun]
  ring

end Work.Kernels.KernelFacts
