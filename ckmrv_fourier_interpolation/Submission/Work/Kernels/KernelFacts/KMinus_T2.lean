/-
# `(T - I)²` annihilates `K_-^{(d)}` in the `τ` variable

CKMRV Theorem 4.9(2): `K_-^{(d)}(·,z)` lies in `Ann(𝓘₋, 𝒫)`, so in particular it is annihilated
by `(T-I)²` at the appropriate weight.  In the explicit pointwise form of
`Work.Kernels.T2op` this is the statement proved here,

  `T2op (fun τ ↦ K_-^{(d)}(τ,z)) = 0`,   `T2op F (τ) = F(τ+2) - 2F(τ+1) + F(τ)`.

Since `K_-^{(d)}(τ,z) = ∑_i ψ_i(τ)·c_i(τ)` with `c_i` the `T`-periodic coefficient function
`Work.Kernels.KMinusCoeff`, the result reduces to the three scalar identities
`T2op ψ_i = 0` for the basis `(ψ_0, ψ_2, ψ_4) = (1, ψ_2, ψ_4)` of CKMRV Proposition 4.3:

* `ψ_0 = 1` is constant;
* `ψ_2 = ξ₂𝓛 + (ξ₂|₂S)𝓛_S` is handled by `psi2_T2`;
* `ψ_4 = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` is handled here, from the transformation laws of the Jacobi theta
  quotients `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴` and the identity
  `ξ₄ + (ξ₄|₄S) + (ξ₄|₄S)(·+1) = 0`.
-/
import Mathlib
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelEquations
import Submission.Work.Kernels.KernelFacts.psi2_T2

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelFacts

/-! ## Transformation laws of `V` under `S`, and of `W` at `τ + 2` -/

/-- `V(-1/τ) = -τ² W(τ)`, the `S`-law of `V = θ₁₀⁴`. -/
lemma VFun_S_smul_km (τ : ℍ) : VFun (ModularGroup.S • τ) = - (τ : ℂ) ^ 2 * WFun τ := by
  simp only [VFun, WFun]
  rw [theta10Fun_S, mul_pow]
  have hpow : ((-Complex.I * (τ : ℂ)) ^ (1/2:ℂ)) ^ 4 = - (τ : ℂ) ^ 2 := by
    rw [← Complex.cpow_nat_mul]
    have hexp : ((4:ℕ):ℂ) * (1/2:ℂ) = ((2:ℕ):ℂ) := by norm_num
    rw [hexp, Complex.cpow_natCast, mul_pow]
    rw [show (-Complex.I : ℂ) ^ 2 = -1 by rw [pow_two, neg_mul_neg, Complex.I_mul_I]]
    ring
  rw [hpow]

/-- `W(τ+2) = W(τ)`. -/
lemma WFun_vadd_two_km (τ : ℍ) : WFun ((2:ℝ) +ᵥ τ) = WFun τ := by
  rw [vadd_one_add_one, WFun_vadd_one, UFun_vadd_one]

/-! ## The `T`-behaviour of `ξ₄ = U² + W² - 2V²` and of its `S`-transform -/

/-- `ξ₄(τ+1) = ξ₄(τ)`. -/
lemma xi4Fun_vadd_one_km (τ : ℍ) : xi4Fun ((1:ℝ) +ᵥ τ) = xi4Fun τ := by
  simp only [xi4Fun, UFun_vadd_one, WFun_vadd_one, VFun_vadd_one]
  ring

/-- `(ξ₄|₄S)(τ) = U(τ)² + V(τ)² - 2W(τ)²`. -/
lemma xi4S_apply_km (τ : ℍ) :
    (xi4Fun ∣[(4:ℤ)] ModularGroup.S) τ = UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2 := by
  rw [slash_S_apply]
  simp only [xi4Fun]
  rw [UFun_S_smul, WFun_S_smul, VFun_S_smul_km]
  have hτ : (τ : ℂ) ≠ 0 := coe_tau_ne_zero τ
  rw [show (τ : ℂ) ^ (-4:ℤ) = ((τ : ℂ) ^ (4:ℤ))⁻¹ from by
    rw [show (-4:ℤ) = -(4:ℤ) from rfl, _root_.zpow_neg]]
  field_simp

/-- `(ξ₄|₄S)(τ+1) = W(τ)² + V(τ)² - 2U(τ)²`. -/
lemma xi4S_vadd_one_km (τ : ℍ) :
    (xi4Fun ∣[(4:ℤ)] ModularGroup.S) ((1:ℝ) +ᵥ τ) =
      WFun τ ^ 2 + VFun τ ^ 2 - 2 * UFun τ ^ 2 := by
  rw [xi4S_apply_km ((1:ℝ) +ᵥ τ)]
  simp only [UFun_vadd_one, WFun_vadd_one, VFun_vadd_one]
  ring

/-- `(ξ₄|₄S)(τ+2) = (ξ₄|₄S)(τ)`. -/
lemma xi4S_vadd_two_km (τ : ℍ) :
    (xi4Fun ∣[(4:ℤ)] ModularGroup.S) ((2:ℝ) +ᵥ τ) =
      (xi4Fun ∣[(4:ℤ)] ModularGroup.S) τ := by
  rw [xi4S_apply_km ((2:ℝ) +ᵥ τ), xi4S_apply_km τ]
  simp only [UFun_vadd_two, WFun_vadd_two_km, VFun_vadd_two]

/-! ## The action of `(T-I)²` on the two summands of `ψ₄` -/

lemma T2op_add_km (F G : ℍ → ℂ) : T2op (F + G) = T2op F + T2op G := by
  ext τ; simp only [T2op, Pi.add_apply]; ring

/-- If `F` is `T`-periodic then `(T-I)²(FG) = F·(T-I)²G`. -/
lemma T2op_mul_periodic_km {F G : ℍ → ℂ} (hF : ∀ τ, F ((1:ℝ) +ᵥ τ) = F τ) :
    T2op (fun τ => F τ * G τ) = fun τ => F τ * T2op G τ := by
  ext τ
  have h2 : F ((2:ℝ) +ᵥ τ) = F τ := by
    rw [vadd_one_add_one, hF ((1:ℝ) +ᵥ τ), hF τ]
  simp only [T2op]
  rw [h2, hF τ]; ring

/-- `(T-I)²𝓛 = 2𝓛_S`. -/
lemma T2op_LogL_km (ℓ : LogLambdaData) : T2op ℓ.L = fun τ => 2 * ℓ.L_S τ := by
  ext τ; simp only [T2op]; rw [L_vadd_two ℓ τ, L_vadd_one ℓ τ]; ring

/-- `(T-I)²((ξ₄|₄S)·𝓛_S) = 2𝓛_S·((ξ₄|₄S) + (ξ₄|₄S)(·+1))`. -/
lemma T2op_xi4S_LogLS_km (ℓ : LogLambdaData) :
    T2op (fun τ => (xi4Fun ∣[(4:ℤ)] ModularGroup.S) τ * ℓ.L_S τ)
      = fun τ => 2 * ℓ.L_S τ * ((xi4Fun ∣[(4:ℤ)] ModularGroup.S) τ
          + (xi4Fun ∣[(4:ℤ)] ModularGroup.S) ((1:ℝ) +ᵥ τ)) := by
  ext τ; simp only [T2op]
  rw [xi4S_vadd_two_km τ, L_S_vadd_two ℓ τ, L_S_vadd_one ℓ τ]; ring

/-- `ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` is annihilated by `(T-I)²` (CKMRV Proposition 4.3). -/
lemma psi4_T2_km (ℓ : LogLambdaData) : T2op (psi4 ℓ) = 0 := by
  have hpsi : psi4 ℓ
      = (fun τ : ℍ => xi4Fun τ * ℓ.L τ)
        + (fun τ : ℍ => (xi4Fun ∣[(4:ℤ)] ModularGroup.S) τ * ℓ.L_S τ) := by
    funext τ; rfl
  rw [hpsi, T2op_add_km, T2op_mul_periodic_km xi4Fun_vadd_one_km, T2op_LogL_km,
    T2op_xi4S_LogLS_km]
  ext τ
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [xi4S_apply_km τ, xi4S_vadd_one_km τ]
  simp only [xi4Fun]
  ring

/-! ## `T`-periodicity of the coefficient function `KMinusCoeff` -/

lemma UpsilonMinus_vadd_one_km (d : ℕ) (z : ℍ) (i j : Fin 3) (τ : ℍ) :
    UpsilonMinus d ((1:ℝ) +ᵥ τ) z i j = UpsilonMinus d τ z i j := by
  simp only [UpsilonMinus]
  split_ifs with h8 h24 <;>
    simp only [PiMat_vadd_one, jInvariantFun_vadd_one]

lemma KMinusCoeff_vadd_one_km (ℓ : LogLambdaData) (d : ℕ) (z : ℍ) (i : Fin 3) (τ : ℍ) :
    KMinusCoeff ℓ d z i ((1:ℝ) +ᵥ τ) = KMinusCoeff ℓ d z i τ := by
  unfold KMinusCoeff
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [UpsilonMinus_vadd_one_km]

/-! ## `(T-I)²` annihilates each component of `ψ⃗` -/

lemma psiVec_T2_km (ℓ : LogLambdaData) (i : Fin 3) :
    T2op (fun τ : ℍ => psiVec ℓ τ i) = 0 := by
  fin_cases i
  · simp only [psiVec]
    ext τ; simp only [T2op]; norm_num
  · simp only [psiVec]; exact psi2_T2 ℓ
  · simp only [psiVec]; exact psi4_T2_km ℓ

/-! ## The main theorem -/

theorem KMinus_T2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : UpperHalfPlane) :
    Work.Kernels.T2op (fun τ : UpperHalfPlane => Work.Kernels.KMinus ℓ d τ z) = 0 := by
  have _ := hd
  have h1 : (fun τ : ℍ => KMinus ℓ d τ z)
      = ∑ i : Fin 3, (fun τ : ℍ => psiVec ℓ τ i * KMinusCoeff ℓ d z i τ) := by
    funext τ
    simp only [Finset.sum_apply]
    exact KMinus_eq_sum ℓ d τ z
  rw [h1]
  refine T2op_sum Finset.univ (fun i _ => ?_)
  exact T2op_mul_of (psiVec_T2_km ℓ i) (fun τ => KMinusCoeff_vadd_one_km ℓ d z i τ)

end Work.Kernels.KernelFacts
