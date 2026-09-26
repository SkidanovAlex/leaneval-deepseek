/-
# The classical modular forms and theta functions, and their membership in `𝒫`

This file fixes the notation for the classical objects used in Sections 4 and 5 of
CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) and records
that the ones with at worst polynomial growth lie in the class `𝒫 = Work.Kernels.InP`.

The definitions follow the paper's normalizations, Section 2.1:

* `E2Fun τ = 1 - 24 ∑_{n ≥ 1} σ₁(n) q^n`  (Mathlib's `EisensteinSeries.E2`),
* `E4Fun τ = 1 + 240 ∑ σ₃(n) q^n`,  `E6Fun τ = 1 - 504 ∑ σ₅(n) q^n`
  (Mathlib's `ModularForm.E₄`, `ModularForm.E₆`),
* `E8Fun = E4Fun ^ 2`, `E10Fun = E4Fun * E6Fun`, `E14Fun = E4Fun ^ 2 * E6Fun`
  (these are forced because the relevant spaces of modular forms are one-dimensional),
* `DeltaFun = (E4Fun ^ 3 - E6Fun ^ 2) / 1728 = q ∏ (1 - q^n)^24`
  (Mathlib's `CuspForm.discriminant`),
* `jInvariantFun = E4Fun ^ 3 / DeltaFun`  (the modular `j`-invariant),
* `theta00Fun`, `theta01Fun`, `theta10Fun`: Jacobi's theta functions
  `θ₀₀ = ∑ q^{n²/2}`, `θ₀₁ = ∑ (-1)^n q^{n²/2}`, `θ₁₀ = ∑ q^{(n+1/2)²/2}`
  (with `q = e^{2πiτ}`), and `UFun = θ₀₀⁴`, `WFun = θ₀₁⁴`, `VFun = θ₁₀⁴`,
* `lambdaFun = VFun / UFun`, `lambdaSFun = WFun / UFun`.
-/
import Mathlib
import Submission.Work.Kernels.SlashDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-- The weight-two Eisenstein series `E₂` as a function of `τ ∈ ℍ`. -/
abbrev E2Fun : ℍ → ℂ := EisensteinSeries.E2

/-- The weight-four Eisenstein series `E₄`. -/
abbrev E4Fun : ℍ → ℂ := ⇑ModularForm.E₄

/-- The weight-six Eisenstein series `E₆`. -/
abbrev E6Fun : ℍ → ℂ := ⇑ModularForm.E₆

/-- The weight-eight Eisenstein series `E₈ = E₄²`. -/
abbrev E8Fun : ℍ → ℂ := fun τ => E4Fun τ ^ 2

/-- The weight-ten Eisenstein series `E₁₀ = E₄E₆`. -/
abbrev E10Fun : ℍ → ℂ := fun τ => E4Fun τ * E6Fun τ

/-- The weight-fourteen Eisenstein series `E₁₄ = E₄²E₆`. -/
abbrev E14Fun : ℍ → ℂ := fun τ => E4Fun τ ^ 2 * E6Fun τ

/-- Ramanujan's cusp form `Δ` of weight `12`, normalized as `(E₄³ - E₆²)/1728`. -/
abbrev DeltaFun : ℍ → ℂ := ⇑CuspForm.discriminant

/-- The modular `j`-invariant, `j = E₄³/Δ`. -/
abbrev jInvariantFun : ℍ → ℂ := fun τ => E4Fun τ ^ 3 / DeltaFun τ

/-- The `q`-parameter `q = e^{2πiτ}` (for reference only; the theta functions below are
defined through Mathlib's `jacobiTheta` and `jacobiTheta₂`). -/
abbrev qParamFun : ℍ → ℂ := fun τ => Complex.exp (2 * Real.pi * Complex.I * τ)

/-- Jacobi's `θ₀₀ = ∑_{n ∈ ℤ} q^{n²/2}`, as a function on `ℍ`. -/
abbrev theta00Fun : ℍ → ℂ := fun τ => jacobiTheta (τ : ℂ)

/-- Jacobi's `θ₀₁ = ∑_{n ∈ ℤ} (-1)^n q^{n²/2}`, expressed as
`jacobiTheta₂ (1/2) τ = ∑_n exp (π i n + π i n²τ)`. -/
abbrev theta01Fun : ℍ → ℂ := fun τ => jacobiTheta₂ (1 / 2) (τ : ℂ)

/-- Jacobi's `θ₁₀ = ∑_{n ∈ ℤ} q^{(n+1/2)²/2}`, expressed as
`e^{πiτ/4} · jacobiTheta₂ (τ/2) τ`. -/
abbrev theta10Fun : ℍ → ℂ :=
  fun τ => Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4) * jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)

/-- `U = θ₀₀⁴`, a modular form of weight `2` for `Γ(2)`. -/
abbrev UFun : ℍ → ℂ := fun τ => theta00Fun τ ^ 4

/-- `W = θ₀₁⁴`, a modular form of weight `2` for `Γ(2)`. -/
abbrev WFun : ℍ → ℂ := fun τ => theta01Fun τ ^ 4

/-- `V = θ₁₀⁴`, a modular form of weight `2` for `Γ(2)`. -/
abbrev VFun : ℍ → ℂ := fun τ => theta10Fun τ ^ 4

/-- The modular lambda function `λ = V/U = θ₁₀⁴/θ₀₀⁴`. -/
abbrev lambdaFun : ℍ → ℂ := fun τ => VFun τ / UFun τ

/-- `λ_S = 1 - λ = W/U = θ₀₁⁴/θ₀₀⁴`. -/
abbrev lambdaSFun : ℍ → ℂ := fun τ => WFun τ / UFun τ

/-- The `ξ₂` of CKMRV, Proposition 4.3: `ξ₂ = U + W`. -/
abbrev xi2Fun : ℍ → ℂ := fun τ => UFun τ + WFun τ

/-- The `ξ₄` of CKMRV, Proposition 4.3: `ξ₄ = U² + W² - 2V²`. -/
abbrev xi4Fun : ℍ → ℂ := fun τ => UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2

/-- The two "exponential-of-log-λ" relations are the content of
`e^{𝓛} = λ`, `e^{𝓛_S} = λ_S`; this is recorded as a predicate on a pair of functions.
It is *not* used as a definition of `𝓛`, `𝓛_S`, which are introduced as data in
`Submission/Work/Kernels/Kernels.lean`. -/
def IsLambdaLog (L L_S : ℍ → ℂ) : Prop :=
  (∀ τ, Complex.exp (L τ) = lambdaFun τ) ∧ (∀ τ, Complex.exp (L_S τ) = lambdaSFun τ)

end Work.Kernels
