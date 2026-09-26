import Mathlib
import Submission.Work.FunctionalEquations.Basic

/-!
# The general-`k₀` version of the interpolation data

`Work.FE.InterpolationSolution n` is the case `k₀ = 1` of the data produced by CKMRV's
construction, with the Fourier expansions and the Section 8 normalisations indexed from
`m ≥ 1`.  For the Leech lattice (`d = 24`) the paper needs `n₀ = 2`: the generating
functions are `o(e^{-2π Im τ})` as `Im τ → ∞`, so the `m = 1` coefficients `a_1, b_1,
ã_1, b̃_1` vanish and the interpolation basis starts at `m = 2` (Theorem 3.1, last
sentence).  This file records the same data with the index set `Set.Ici k₀` and the
sample radii `√(2m)`, `m ≥ k₀`, so that `k₀ = 1` recovers `InterpolationSolution` and
`k₀ = 2` covers the Leech lattice.

The fields are indexed by `SampleIdx k₀ = Set.Ici k₀ × Fin 4`, with the same slot
convention as `Work.Core.coeffs`: slot `0` is `a_n`, slot `1` is `ã_n`, slot `2` is
`b_n` and slot `3` is `b̃_n`.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

noncomputable section

structure InterpolationSolutionGen (n : ℕ) [NeZero n] (k₀ : ℕ) extends FunctionalEquationSolution n where
  /-- The four families of coefficient functions. -/
  basis : SampleIdx k₀ → RSch n
  /-- The expansion of `F` (paper (3.1)). -/
  expansion_F : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
    F τ x = (∑' m : Set.Ici k₀, (basis (m, 0)).1 x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 2)).1 x * dirichletTerm m.1 τ
  /-- The expansion of `F̃` (paper (3.2)). -/
  expansion_Ftilde : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
    Ftilde τ x = (∑' m : Set.Ici k₀, (basis (m, 1)).1 x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 3)).1 x * dirichletTerm m.1 τ
  /-- The expansion of `F` may be differentiated termwise in `x`. -/
  expansion_F_radialDeriv : ∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
    radialDeriv ℓ (F τ) x =
      (∑' m : Set.Ici k₀, radialDeriv ℓ (⇑(basis (m, 0)).1) x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 2)).1) x
            * dirichletTerm m.1 τ
  /-- The expansion of `F̃` may be differentiated termwise in `x`. -/
  expansion_Ftilde_radialDeriv : ∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
    radialDeriv ℓ (Ftilde τ) x =
      (∑' m : Set.Ici k₀, radialDeriv ℓ (⇑(basis (m, 1)).1) x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 3)).1) x
            * dirichletTerm m.1 τ
  /-- The Fourier transform of `a_n` is `ã_n` (paper Section 8: `ã = â`). -/
  fourier_basis : ∀ m : Set.Ici k₀,
    (basis (m, 1)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1
  /-- The Fourier transform of `b_n` is `b̃_n` (paper Section 8: `b̃ = b̂`). -/
  fourier_basis' : ∀ m : Set.Ici k₀,
    (basis (m, 3)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1
  /-- Normalisation of `F` at the sample radii (Section 8). -/
  value_F : ∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
    F τ (samplePoint (n := n) (m.1 : ℝ)) = dirichletTerm m.1 τ
  /-- Normalisation of `F̃` at the sample radii (Section 8). -/
  value_Ftilde : ∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
    Ftilde τ (samplePoint (n := n) (m.1 : ℝ)) = 0
  /-- Normalisation of the radial derivative of `F` at the sample radii (Section 8). -/
  value_radialDeriv_F : ∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
    radialDeriv 1 (F τ) (samplePoint (n := n) (m.1 : ℝ))
      = (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ)) * dirichletTerm m.1 τ
  /-- Normalisation of the radial derivative of `F̃` at the sample radii (Section 8). -/
  value_radialDeriv_Ftilde : ∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
    radialDeriv 1 (Ftilde τ) (samplePoint (n := n) (m.1 : ℝ)) = 0
  /-- The radial seminorms of the coefficient functions grow at most polynomially
  (last sentence of Theorem 3.1). -/
  growth_radial : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
    ∀ (m : Set.Ici k₀) (j : Fin 4) (x : E n),
      ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N


end

end Work.FE
