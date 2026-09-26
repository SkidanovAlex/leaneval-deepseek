/-
# Definitions for the local biholomorphy of `λ`

The modular lambda function `λ = θ₁₀⁴/θ₀₀⁴` is a local biholomorphism at every point of `ℍ`.
The proof goes through the classical identity

  `λ'(τ) = π i λ(τ) (1 - λ(τ)) θ₀₀(τ)⁴`,

equivalently the statement that

  `ρ(τ) = λ'(τ) / (λ(τ) (1 - λ(τ)) θ₀₀(τ)⁴)`

is the constant `π i`.  Since `λ` and `θ₀₀⁴` transform under `SL(2, ℤ)` with weight `0` and `2`
respectively, `ρ` is `SL(2, ℤ)`-invariant of weight `0` and holomorphic on `ℍ`; being bounded at
the cusp, it is a level-one modular form of weight `0`, hence constant by
`ModularFormClass.levelOne_weight_zero_const`.  The constant is non-zero because otherwise `λ`
would be constant, contradicting `λ(-1/τ) = 1 - λ(τ)` and `λ(τ+1) = λ(τ)/(λ(τ)-1)`.

The boundedness at the cusp is proved by writing `λ = F ∘ 𝕢 2` where `F` is the `q`-expansion
(cusp function) of `λ`, analytic at `0` with `F(0) = 0` and `F'(0) = 16 ≠ 0`, so that
`λ'(z)/λ(z) = π i F'(q)/ (F(q)/q)` is bounded near `q = 0`.

This file collects the definitions used by that argument.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaBasic
import Submission.Work.Kernels.LogLambda.LogConstruct
import Submission.Work.Modular.modularForm_of_slash_invariant

noncomputable section

open UpperHalfPlane Filter Topology Complex
open scoped UpperHalfPlane ModularForm

namespace Work.Rigidity

open Work.Kernels Work.Kernels.LogLambda

/-- The function `ρ(z) = λ'(z)/(λ(z)(1-λ(z))θ₀₀(z)⁴)`, extended by junk values off the
upper half plane. -/
def rhoC (z : ℂ) : ℂ :=
  deriv lamC z / (lamC z * (1 - lamC z) * (thetaC00 z) ^ 4)

/-- `ρ` as a function on the upper half plane. -/
def rho (τ : ℍ) : ℂ := rhoC (τ : ℂ)

/-- The `q`-expansion (cusp function) of `λ`, a function of `q = exp (π i τ)`. -/
def Flam : ℂ → ℂ := UpperHalfPlane.cuspFunction 2 (fun τ : ℍ => lambdaFun τ)

end Work.Rigidity
