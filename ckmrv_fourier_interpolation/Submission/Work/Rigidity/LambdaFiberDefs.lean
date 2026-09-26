/-
# Definitions for the Hauptmodul property of `λ = θ₁₀⁴/θ₀₀⁴`

The modular lambda function `λ = Work.Kernels.lambdaFun` is invariant under the principal
congruence subgroup `Γ(2)`.  This file fixes the notation used by the proof of
`Work.Rigidity.lambda_fiber_orbit` (the statement that the fibres of `λ` are `Γ(2)`-orbits):

* `FDom = {τ | |Re τ| ≤ 1, ‖τ‖² ≥ |Re τ|}`, the standard closed fundamental domain of `Γ(2)`;
  its interior is `FDomInt`, and `λ` is real on `FDom \ FDomInt`;
* `reflPt τ = -τ̄`, the reflection in the imaginary axis;
* `lambdaFun_gamma2_invariant`: `λ` is invariant under `Γ(2)`.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaTargets
import Submission.Work.Rigidity.LambdaBasic
import Submission.Work.Rigidity.gamma2_generators

namespace Work.Rigidity

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups

noncomputable section

open Work.Kernels Work.Kernels.LogLambda

/-- The closed fundamental domain `F = {τ || Re τ| ≤ 1, ‖τ‖² ≥ |Re τ|}` of `Γ(2)`. -/
def FDom : Set ℍ := {τ | |(τ : ℂ).re| ≤ 1 ∧ ‖(τ : ℂ)‖ ^ 2 ≥ |(τ : ℂ).re|}

/-- The interior of the fundamental domain `F`. -/
def FDomInt : Set ℍ := {τ | |(τ : ℂ).re| < 1 ∧ ‖(τ : ℂ)‖ ^ 2 > |(τ : ℂ).re|}

/-- Reflection in the imaginary axis. -/
def reflPt (τ : ℍ) : ℍ :=
  ⟨-(starRingEnd ℂ) (τ : ℂ), by
    rw [Complex.neg_im, Complex.conj_im, neg_neg]
    exact τ.im_pos⟩

@[simp] lemma reflPt_coe (τ : ℍ) : ((reflPt τ : ℍ) : ℂ) = -(starRingEnd ℂ) (τ : ℂ) := rfl

/-- **The fibre of `λ` over `w` is a single `Γ(2)`-orbit.**  This is the Hauptmodul property
of `λ`, proved in `Work.Rigidity.lambda_fiber_orbit`. -/
def FiberGood (w : ℂ) : Prop :=
  ∀ τ τ' : ℍ, lambdaFun τ = w → lambdaFun τ' = w →
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ = τ'

/-- **`λ` is invariant under `Γ(2)`.** -/
theorem lambdaFun_gamma2_invariant :
    ∀ γ ∈ CongruenceSubgroup.Gamma 2, ∀ τ : ℍ, lambdaFun (γ • τ) = lambdaFun τ := by
  let H : Subgroup SL(2,ℤ) :=
    { carrier := {γ | ∀ τ : ℍ, lambdaFun (γ • τ) = lambdaFun τ}
      one_mem' := by intro τ; simp
      mul_mem' := by
        intro a b ha hb τ
        rw [mul_smul, ha, hb]
      inv_mem' := by
        intro a ha τ
        have h := ha (a⁻¹ • τ)
        rw [smul_inv_smul] at h
        exact h.symm }
  have hsq : ModularGroup.T * ModularGroup.T ∈ H := by
    intro τ
    show lambdaFun ((ModularGroup.T * ModularGroup.T) • τ) = lambdaFun τ
    rw [← pow_two]
    exact lambdaFun_T2 τ
  have hsts : ModularGroup.S * (ModularGroup.T * ModularGroup.T) * ModularGroup.S ∈ H := by
    intro τ
    show lambdaFun ((ModularGroup.S * (ModularGroup.T * ModularGroup.T) * ModularGroup.S) • τ)
      = lambdaFun τ
    rw [← pow_two (ModularGroup.T)]
    rw [mul_smul, mul_smul]
    rw [lambdaFun_S, lambdaSFun_T2, lambdaSFun_S]
  have hss : ModularGroup.S * ModularGroup.S ∈ H := by
    intro τ
    show lambdaFun ((ModularGroup.S * ModularGroup.S) • τ) = lambdaFun τ
    rw [SS_eq_neg_one, ← ModularGroup.SL_neg_smul]
    simp
  have hle : CongruenceSubgroup.Gamma 2 ≤ H := by
    rw [gamma2_generators]
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hsq
    · exact hsts
    · exact hss
  intro γ hγ τ
  exact hle hγ τ

end

end Work.Rigidity
