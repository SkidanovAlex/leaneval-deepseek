import Submission.Work.FunctionalEquations.Basic
import Submission.Work.CKFinal.Shadow.Util

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FE
export _root_.Work.FE (E radialDeriv radialSeminorm dirichletTerm slashFactor rate samplePoint GaussiansDense)
end Work.FE

/-!
# Functional equations and the interpolation basis (CKMRV, section 3.1)

This file sets up the vocabulary for the analytic bridge in CKMRV
(*Universal optimality of the E8 and Leech lattices and interpolation formulas*,
Ann. of Math. 196 (2022)), namely Theorem 3.1: a well-behaved solution of the
functional equations implies the interpolation formula.

## Conventions

* `E n` denotes `EuclideanSpace ℝ (Fin n)`.
* `radialDeriv ℓ g x` is the `ℓ`-th derivative of the radial profile
  `r ↦ g (realIncl r)` evaluated at `r = ‖x‖`; for a radial function this is the
  paper's `D_x^ℓ g(x)`.
* `dirichletTerm m τ = exp (2 π i m τ)`.
* `slashFactor n τ = (i/τ)^(n/2)` with the principal branch of the complex power;
  for `τ` in the upper half plane the base `i/τ` has positive real part, and this
  agrees with the constant `(π/b)^(n/2)` at `b = -π i τ` produced by Mathlib's
  Gaussian Fourier transform `fourier_gaussian_innerProductSpace`.

## Main definitions

* `Work.FE.FunctionalEquationSolution n`: hypotheses (i)--(v) of Theorem 3.1.
* `Work.FE.InterpolationSolution n`: the same, together with the data that the
  paper's construction produces for them: the Fourier expansions with radial
  Schwartz coefficients, the polynomial growth of the coefficients, the
  normalisations `F(τ,√(2m)) = e^{2πimτ}`, `F̃(τ,√(2m)) = 0` and their radial
  derivatives used in Section 8 to deduce the Kronecker delta pattern, and the
  Fourier transform relations `ã = â`, `b̃ = b̂`.

`Work.FE.interpolationBasis_of_functionalEquations` (in `Main.lean`) converts an
`InterpolationSolution n` into a `Work.Core.InterpolationBasis n 1`.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

noncomputable section

/-- Hypotheses (i)--(v) of CKMRV Theorem 3.1. -/
structure FunctionalEquationSolution (n : ℕ) [NeZero n] where
  /-- The generating function `F(τ,x)`. -/
  F : ℂ → E n → ℂ
  /-- The generating function `F̃(τ,x)`. -/
  Ftilde : ℂ → E n → ℂ
  /-- (i) `F` is holomorphic in `τ` on the upper half plane, for each `x`. -/
  holomorphic_F : ∀ x, DifferentiableOn ℂ (fun τ : ℂ => F τ x) {τ : ℂ | 0 < τ.im}
  /-- (i) `F̃` is holomorphic in `τ` on the upper half plane, for each `x`. -/
  holomorphic_Ftilde : ∀ x, DifferentiableOn ℂ (fun τ : ℂ => Ftilde τ x) {τ : ℂ | 0 < τ.im}
  /-- (i) `F` is smooth in `x`, for each `τ`. -/
  smooth_F : ∀ τ, ContDiff ℝ ∞ (F τ)
  /-- (i) `F̃` is smooth in `x`, for each `τ`. -/
  smooth_Ftilde : ∀ τ, ContDiff ℝ ∞ (Ftilde τ)
  /-- (ii) `F` is radial in `x`, for each `τ`. -/
  radial_F : ∀ τ, Radial (F τ)
  /-- (ii) `F̃` is radial in `x`, for each `τ`. -/
  radial_Ftilde : ∀ τ, Radial (Ftilde τ)
  /-- (iii) radial derivative growth bounds for `F`. -/
  growth_F : ∀ k ℓ : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
    ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      ‖x‖ ^ k * ‖radialDeriv ℓ (F τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ
  /-- (iii) radial derivative growth bounds for `F̃`. -/
  growth_Ftilde : ∀ k ℓ : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
    ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      ‖x‖ ^ k * ‖radialDeriv ℓ (Ftilde τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ
  /-- (iv) uniform bound for `F` in the strip `-1 ≤ Re τ ≤ 1`. -/
  uniform_F : ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧ ∀ (τ : ℂ) (x : E n),
    0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 → ‖F τ x‖ ≤ α * τ.im ^ (-β)
  /-- (iv) uniform bound for `F̃` in the strip `-1 ≤ Re τ ≤ 1`. -/
  uniform_Ftilde : ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧ ∀ (τ : ℂ) (x : E n),
    0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 → ‖Ftilde τ x‖ ≤ α * τ.im ^ (-β)
  /-- (v) the second difference equation for `F`. -/
  recur_F : ∀ (τ : ℂ) (x : E n), 0 < τ.im → F (τ + 2) x - 2 * F (τ + 1) x + F τ x = 0
  /-- (v) the second difference equation for `F̃`. -/
  recur_Ftilde : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
    Ftilde (τ + 2) x - 2 * Ftilde (τ + 1) x + Ftilde τ x = 0
  /-- (v) the Poisson-summation functional equation. -/
  functional_equation : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
    F τ x + slashFactor n τ * Ftilde (-1 / τ) x = Work.Core.gaussianFun n τ x

/-- The data produced by the paper's construction, on top of the hypotheses (i)--(v) of
Theorem 3.1.

The paper's Section 3.1 (Steps 1 and 2) produces the two Fourier expansions with radial
Schwartz coefficients `a_n, b_n, ã_n, b̃_n`, together with polynomial growth of the radial
seminorms (the last sentence of Theorem 3.1).  Section 8 additionally uses the
normalisations `F(τ,√(2m)) = e^{2π i m τ}`, `F̃(τ,√(2m)) = 0` and the corresponding radial
derivative computations, together with the relation `ã = â`, `b̃ = b̂`, to deduce the
Kronecker delta pattern for the samples of the basis.

The four coefficient families are collected in a single family
`basis : SampleIdx 1 → RSch n`, indexed exactly as the sample index of
`Work.Core.coeffs`, i.e. slot `0` is `a_n`, slot `1` is `ã_n`, slot `2` is `b_n` and
slot `3` is `b̃_n`. -/
structure InterpolationSolution (n : ℕ) [NeZero n] extends FunctionalEquationSolution n where
  /-- The four families of coefficient functions. -/
  basis : SampleIdx 1 → RSch n
  /-- The expansion of `F` (paper (3.1)). -/
  expansion_F : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
    F τ x = (∑' m : Set.Ici (1 : ℕ), (basis (m, 0)).1 x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * (basis (m, 2)).1 x * dirichletTerm m.1 τ
  /-- The expansion of `F̃` (paper (3.2)). -/
  expansion_Ftilde : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
    Ftilde τ x = (∑' m : Set.Ici (1 : ℕ), (basis (m, 1)).1 x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * (basis (m, 3)).1 x * dirichletTerm m.1 τ
  /-- The expansion of `F` may be differentiated termwise in `x`. -/
  expansion_F_radialDeriv : ∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
    radialDeriv ℓ (F τ) x =
      (∑' m : Set.Ici (1 : ℕ), radialDeriv ℓ (⇑(basis (m, 0)).1) x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 2)).1) x
            * dirichletTerm m.1 τ
  /-- The expansion of `F̃` may be differentiated termwise in `x`. -/
  expansion_Ftilde_radialDeriv : ∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
    radialDeriv ℓ (Ftilde τ) x =
      (∑' m : Set.Ici (1 : ℕ), radialDeriv ℓ (⇑(basis (m, 1)).1) x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 3)).1) x
            * dirichletTerm m.1 τ
  /-- The Fourier transform of `a_n` is `ã_n` (paper Section 8: `ã = â`). -/
  fourier_basis : ∀ m : Set.Ici (1 : ℕ),
    (basis (m, 1)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1
  /-- The Fourier transform of `b_n` is `b̃_n` (paper Section 8: `b̃ = b̂`). -/
  fourier_basis' : ∀ m : Set.Ici (1 : ℕ),
    (basis (m, 3)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1
  /-- Normalisation of `F` at the sample radii (Section 8). -/
  value_F : ∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
    F τ (samplePoint (n := n) (m.1 : ℝ)) = dirichletTerm m.1 τ
  /-- Normalisation of `F̃` at the sample radii (Section 8). -/
  value_Ftilde : ∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
    Ftilde τ (samplePoint (n := n) (m.1 : ℝ)) = 0
  /-- Normalisation of the radial derivative of `F` at the sample radii (Section 8). -/
  value_radialDeriv_F : ∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
    radialDeriv 1 (F τ) (samplePoint (n := n) (m.1 : ℝ))
      = (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ)) * dirichletTerm m.1 τ
  /-- Normalisation of the radial derivative of `F̃` at the sample radii (Section 8). -/
  value_radialDeriv_Ftilde : ∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
    radialDeriv 1 (Ftilde τ) (samplePoint (n := n) (m.1 : ℝ)) = 0
  /-- The radial seminorms of the coefficient functions grow at most polynomially
  (last sentence of Theorem 3.1). -/
  growth_radial : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
    ∀ (m : Set.Ici (1 : ℕ)) (j : Fin 4) (x : E n),
      ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N

end

end Work.FE


end Work.CKFinal.Shadow
