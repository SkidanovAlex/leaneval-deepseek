import Mathlib
import Submission.Work.Asymptotics.KhatE1.Bracket24E2_defs

/-!
# Auxiliary definitions for `Bracket24E2Prime_bound`

This module collects the definitions shared between the target
`Work.Asymptotics.KhatE1Core.Bracket24E2Prime_bound` and its helper lemmas.

Recall (`Submission/Work/Asymptotics/KhatE1/Bracket24E2_defs.lean`) that
`Bracket24E2 ℓ τ z = jInvariantFun τ * Kappa ℓ τ z + Rest ℓ τ z`, and that the
truncations `KappaHat`/`RestHat` (with `E₄ ↦ 1+240q`, `E₆ ↦ 1-504q`, `E₂ ↦ 1-24q`,
`ψ₂ ↦ 2Λ+(48Λ+408)q`, `ψ₄ ↦ 2Λ-(288Λ+744)q`, `Δ ↦ q`) satisfy the exact identity
`A1q q * KappaHatP q L τ z C π + q * RestHatP q L τ z C π = q² * Poly2 q τ z C π`
(`kappahat_identity`), which after division by `(πz)²` reads
`A1q q * κ̂ + q * ρ̂ = q² Δ₂`.

Here we fix the notation used in the bound: `khatDef`/`rhatDef` are the truncated pieces at
`(τ, z)`, `devA1Fun` is `E₄³ - A₁`, `poly2Fun` is `Π₂` and `delta2Fun = Π₂/(πz)²`.
-/

namespace Work.Asymptotics.KhatE1Core

open Work.Asymptotics.KhatE1

/-- `κ̂ = KappaHat (q(τ)) (Λ) (τ) (z) (c) π`, the truncation of the `j`-coefficient. -/
noncomputable def khatDef (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
  KappaHat (Work.Kernels.qParamFun τ) (cuspLin ℓ τ) (τ : ℂ) (z : ℂ)
    (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ)

/-- `ρ̂ = RestHat (q(τ)) (Λ) (τ) (z) (c) π`, the truncation of the `j`-free part. -/
noncomputable def rhatDef (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
  RestHat (Work.Kernels.qParamFun τ) (cuspLin ℓ τ) (τ : ℂ) (z : ℂ)
    (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ)

/-- `E₄(τ)³ - A₁(q(τ))` with `A₁ = (1+240q)³`. -/
noncomputable def devA1Fun (τ : UpperHalfPlane) : ℂ :=
  (Work.Kernels.E4Fun τ) ^ 3 - A1q (Work.Kernels.qParamFun τ)

/-- `Π₂(q(τ), τ, z, c, π)`. -/
noncomputable def poly2Fun (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
  Poly2 (Work.Kernels.qParamFun τ) (τ : ℂ) (z : ℂ)
    (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ)

/-- `Δ₂ = Π₂/(πz)²`. -/
noncomputable def delta2Fun (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
  Delta2 (Work.Kernels.qParamFun τ) (τ : ℂ) (z : ℂ)
    (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ)

end Work.Asymptotics.KhatE1Core
