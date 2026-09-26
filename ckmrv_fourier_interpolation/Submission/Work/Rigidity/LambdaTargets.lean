/-
# The target statements of the lambda-descent development

The main theorem `Work.Rigidity.lambda_descent` (the Hauptmodul property of the modular
lambda function `λ = θ₁₀⁴/θ₀₀⁴` for `Γ(2)`) is assembled from the Prop-valued statements
packaged here, so that each can be stated and quoted without notation friction.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaBasic

noncomputable section

open UpperHalfPlane ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

open Work.Kernels

/-- `λ` takes every value in `ℂ∖{0,1}`. -/
def LambdaSurjective : Prop :=
  ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∃ τ : ℍ, lambdaFun τ = w

/-- The fibres of `λ` are `Γ(2)`-orbits. -/
def LambdaFiberOrbits : Prop :=
  ∀ τ₁ τ₂ : ℍ, lambdaFun τ₁ = lambdaFun τ₂ →
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂

/-- **`λ` is a Hauptmodul for `Γ(2)`**: it is surjective onto `ℂ∖{0,1}` and its fibres
are the `Γ(2)`-orbits. -/
def LambdaHauptmodul : Prop := LambdaSurjective ∧ LambdaFiberOrbits

/-- `λ` is invariant under `Γ(2)`. -/
def LambdaGammaTwoInvariant : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma 2, ∀ τ : ℍ, lambdaFun (γ • τ) = lambdaFun τ

/-- `λ` is a local biholomorphism at every point of `ℍ`: there is a holomorphic local
right inverse defined near `λ τ₀`. -/
def LambdaLocalInverse : Prop :=
  ∀ τ₀ : ℍ, ∃ (φ : ℂ → ℂ) (V : Set ℂ), V ∈ 𝓝 (lambdaFun τ₀) ∧
    DifferentiableOn ℂ φ V ∧ φ (lambdaFun τ₀) = (τ₀ : ℂ) ∧
    ∀ᶠ w in 𝓝 (lambdaFun τ₀), 0 < (φ w).im ∧
      ∀ hw : 0 < (φ w).im, lambdaFun ⟨φ w, hw⟩ = w

/-- The classical identity `θ₁₀⁴ + θ₀₁⁴ = θ₀₀⁴`, i.e. `λ_S = 1 - λ`. -/
def ThetaFourthIdentity : Prop :=
  ∀ τ : ℍ, Work.Kernels.theta10Fun τ ^ 4 + Work.Kernels.theta01Fun τ ^ 4
    = Work.Kernels.theta00Fun τ ^ 4

end Work.Rigidity
