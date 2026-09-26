import ChallengeDeps

/-!
# Shared vocabulary for the CKMRV Fourier-interpolation development

The challenge's own definitions (`Radial`, `coeffs`, `RapidlyDecreasing`, `CKMRV`, ...)
live in `ChallengeDeps.lean` and are used exactly as they stand.
-/

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap

namespace Work.Core

/-- The complex Gaussian `x ↦ exp (π i τ ‖x‖ ^ 2)` on `R^n`. -/
noncomputable def gaussianFun (n : ℕ) (τ : ℂ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  Complex.exp (↑Real.pi * Complex.I * τ * (↑(‖x‖ ^ 2) : ℂ))

/-- The index type of the four sample sequences. -/
abbrev SampleIdx (k₀ : ℕ) : Type := Set.Ici k₀ × Fin 4

/-- A radial complex-valued Schwartz function on `R^n`. -/
abbrev RSch (n : ℕ) : Type :=
  {f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ // Radial f}

/-- The four rapidly decreasing sample sequences of a radial Schwartz function. -/
abbrev RSample (k₀ : ℕ) : Type :=
  {a : SampleIdx k₀ → ℂ // RapidlyDecreasingSamples a}

/-- Interpolation data as constructed in CKMRV: a family of radial Schwartz functions
indexed by the samples, whose samples are Kronecker deltas, whose Schwartz seminorms
grow at most polynomially in the index, and which reconstruct every radial Schwartz
function from its samples (the interpolation formula). -/
structure InterpolationBasis (n k₀ : ℕ) [NeZero n] where
  /-- The interpolation basis, indexed by the sample index. -/
  basis : SampleIdx k₀ → RSch n
  /-- The samples of the basis form the Kronecker delta. -/
  delta : ∀ i, coeffs n k₀ (basis i).1 = fun j => if j = i then (1 : ℂ) else 0
  /-- Every Schwartz seminorm of the basis grows at most polynomially in the index. -/
  growth : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
    ∀ i : SampleIdx k₀, (SchwartzMap.seminorm ℂ k l) (basis i).1
      ≤ C * ((i.1.1 : ℝ) + 1) ^ N
  /-- The interpolation formula: every radial Schwartz function is the sum of its
  samples times the basis. -/
  formula : ∀ f : RSch n, ∀ x : EuclideanSpace ℝ (Fin n),
    f.1 x = ∑' i : SampleIdx k₀, (coeffs n k₀ f.1 i) * (basis i).1 x

end Work.Core
