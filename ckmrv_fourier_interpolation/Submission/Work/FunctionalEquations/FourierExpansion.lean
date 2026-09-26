import Mathlib
import Submission.Work.FunctionalEquations.Basic

/-!
# The Fourier transform in `x` of the generating functions, through their expansions

If `F(τ,x) = ∑_m a_m(x) e^{2πimτ} + 2πiτ ∑_m √(2m) b_m(x) e^{2πimτ}`, then the Fourier
transform of `x ↦ F(τ,x)` is the same Dirichlet series with `a_m`, `b_m` replaced by their
Fourier transforms.  These definitions make that object available without knowing that
`x ↦ F(τ,x)` is a Schwartz function: the series is written down directly, using that the
Fourier transform of a Schwartz coefficient function is again a Schwartz function.

This is the object `𝓕_x F` of Section 8 of the paper, used to show that `(𝓕_x F̃, 𝓕_x F)`
solves the same three functional equations as `(F, F̃)`.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

noncomputable section

/-- `𝓕_x F`, computed through the expansion: the Dirichlet series whose coefficients are
the Fourier transforms of the coefficient functions `a_m`, `b_m`. -/
def fourierExpansionGen {n : ℕ} [NeZero n] (k₀ : ℕ) (basis : SampleIdx k₀ → RSch n)
    (τ : ℂ) (x : E n) : ℂ :=
  (∑' m : Set.Ici k₀,
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x * dirichletTerm m.1 τ)
    + (2 * (Real.pi : ℂ) * Complex.I * τ)
      * ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
          * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
          * dirichletTerm m.1 τ

/-- `𝓕_x F̃`, computed through the expansion. -/
def fourierExpansionTildeGen {n : ℕ} [NeZero n] (k₀ : ℕ) (basis : SampleIdx k₀ → RSch n)
    (τ : ℂ) (x : E n) : ℂ :=
  (∑' m : Set.Ici k₀,
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x * dirichletTerm m.1 τ)
    + (2 * (Real.pi : ℂ) * Complex.I * τ)
      * ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
          * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
          * dirichletTerm m.1 τ

/-- The `k₀ = 1` case of `fourierExpansionGen`. -/
abbrev fourierExpansion {n : ℕ} [NeZero n] (basis : SampleIdx 1 → RSch n) : ℂ → E n → ℂ :=
  fourierExpansionGen 1 basis

/-- The `k₀ = 1` case of `fourierExpansionTildeGen`. -/
abbrev fourierExpansionTilde {n : ℕ} [NeZero n] (basis : SampleIdx 1 → RSch n) : ℂ → E n → ℂ :=
  fourierExpansionTildeGen 1 basis

end

end Work.FE
