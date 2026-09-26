import Submission.Work.FunctionalEquations.Gap
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow


/-!
# The exact gap between the functional equations and the interpolation basis

`Work.FE.FunctionalEquationSolution` is hypotheses (i)--(v) of CKMRV Theorem 3.1,
verbatim.  `Work.FE.InterpolationSolution` adds

* the data that the paper's Steps 1 and 2 produce from those hypotheses: two Fourier
  expansions with radial Schwartz coefficients, the termwise radial differentiability of
  the expansions, and polynomial growth of the radial seminorms of the coefficients
  (the last sentence of Theorem 3.1);
* the normalisations of Section 8: `F(τ,√(2m)) = e^{2πimτ}`, `F̃(τ,√(2m)) = 0`, and the
  corresponding values of the radial derivatives, together with the relations
  `ã = â`, `b̃ = b̂`;

`Work.FE.interpolationBasis_of_functionalEquations` converts an `InterpolationSolution`
into a `Work.Core.InterpolationBasis n 1`; the density input of Step 3 (paper Lemma 3.3)
is the *theorem* `Work.FE.gaussiansDense`.  This file records, without proof, the two
statements that would close the gap.

## Why the extra data is not redundant

The `delta` field of `Work.Core.InterpolationBasis n 1` asserts that the samples of the
`i`-th basis function are the `i`-th Kronecker delta.  Write `Φ` for the sampling map and
`β` for the basis, and let `M` be the sampling matrix `M i j = (Φ (β j)) i`.  The
interpolation formula (a consequence of hypotheses (i)--(v) alone) says that `Ψ := β` is a
left inverse of `Φ`, i.e. `∑ i, (Φ f) i • β i = f` for every radial Schwartz `f`; applied
to `f = β j` and then to `Φ` it gives `M = M * M`, i.e. `M` is idempotent.  The `delta`
field is exactly `M = 1`, which is equivalent to `Ψ` being a right inverse of `Φ` as well,
i.e. to surjectivity of `Φ` on the radial Schwartz space.

Surjectivity of `Φ` is not a consequence of the functional equations in general: it is the
dimension-specific content of Section 8 of the paper, where the uniqueness lemma
`lem:noPsolutions` (proved there for weights `4` and `12`, i.e. dimensions `8` and `24`) is
used to show `F(τ,√(2m)) = e^{2πimτ}` and its radial-derivative analogue, equivalently the
`M = 1` statement.  Accordingly we retain the Section 8 normalisations and the
Fourier-transform relations as fields of `InterpolationSolution`.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open Filter Topology
open scoped FourierTransform SchwartzMap

/-- **Paper Steps 1--2 for one solution.**  The coefficient family with the two Fourier
expansions (3.1), (3.2), their termwise radial differentiability, and the polynomial
growth of the radial seminorms of the coefficients.  This is the analytic half of the
gap; at a single `x` it is `Work.FunctionalEquations.DirichletExpansion` together with
`Work.FunctionalEquations.ExpansionFromFunctionalEquations`. -/
def ExpansionData (n : ℕ) [NeZero n] (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) : Prop :=
  (∀ (τ : ℂ) (x : E n), 0 < τ.im →
      S.F τ x = (∑' m : Set.Ici (1 : ℕ), (basis (m, 0)).1 x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * (basis (m, 2)).1 x * dirichletTerm m.1 τ) ∧
  (∀ (τ : ℂ) (x : E n), 0 < τ.im →
      S.Ftilde τ x = (∑' m : Set.Ici (1 : ℕ), (basis (m, 1)).1 x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * (basis (m, 3)).1 x * dirichletTerm m.1 τ) ∧
  (∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
      radialDeriv ℓ (S.F τ) x =
        (∑' m : Set.Ici (1 : ℕ), radialDeriv ℓ (⇑(basis (m, 0)).1) x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 2)).1) x
              * dirichletTerm m.1 τ) ∧
  (∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
      radialDeriv ℓ (S.Ftilde τ) x =
        (∑' m : Set.Ici (1 : ℕ), radialDeriv ℓ (⇑(basis (m, 1)).1) x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 3)).1) x
              * dirichletTerm m.1 τ) ∧
  (∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ (m : Set.Ici (1 : ℕ)) (j : Fin 4) (x : E n),
        ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N)

/-- **Paper Section 8.**  The normalisations at the sample radii and the Fourier-transform
relations `ã = â`, `b̃ = b̂`.  This is the dimension-specific half of the gap: the
normalisations follow from the uniqueness lemma `lem:noPsolutions` of the paper (proved
there for weights `4` and `12`, i.e. dimensions `8` and `24`), applied to the specific
solutions constructed from quasimodular forms. -/
def Section8Data (n : ℕ) [NeZero n] (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) : Prop :=
  (∀ m : Set.Ici (1 : ℕ),
      (basis (m, 1)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) ∧
  (∀ m : Set.Ici (1 : ℕ),
      (basis (m, 3)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) ∧
  (∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
      S.F τ (samplePoint (n := n) (m.1 : ℝ)) = dirichletTerm m.1 τ) ∧
  (∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
      S.Ftilde τ (samplePoint (n := n) (m.1 : ℝ)) = 0) ∧
  (∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
      radialDeriv 1 (S.F τ) (samplePoint (n := n) (m.1 : ℝ))
        = (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ)) * dirichletTerm m.1 τ) ∧
  (∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
      radialDeriv 1 (S.Ftilde τ) (samplePoint (n := n) (m.1 : ℝ)) = 0)

/-! ## The general-`k₀` versions of the gap data -/

/-- `Work.FE.ExpansionData` with the index set `Set.Ici k₀`: the Fourier expansions and the
polynomial growth of the radial seminorms of the coefficients (Steps 1--2). -/
def ExpansionDataGen (n : ℕ) [NeZero n] (k₀ : ℕ) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) : Prop :=
  (∀ (τ : ℂ) (x : E n), 0 < τ.im →
      S.F τ x = (∑' m : Set.Ici k₀, (basis (m, 0)).1 x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 2)).1 x * dirichletTerm m.1 τ) ∧
  (∀ (τ : ℂ) (x : E n), 0 < τ.im →
      S.Ftilde τ x = (∑' m : Set.Ici k₀, (basis (m, 1)).1 x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 3)).1 x * dirichletTerm m.1 τ) ∧
  (∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
      radialDeriv ℓ (S.F τ) x =
        (∑' m : Set.Ici k₀, radialDeriv ℓ (⇑(basis (m, 0)).1) x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 2)).1) x
              * dirichletTerm m.1 τ) ∧
  (∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
      radialDeriv ℓ (S.Ftilde τ) x =
        (∑' m : Set.Ici k₀, radialDeriv ℓ (⇑(basis (m, 1)).1) x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 3)).1) x
              * dirichletTerm m.1 τ) ∧
  (∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ (m : Set.Ici k₀) (j : Fin 4) (x : E n),
        ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N)

/-- `Work.FE.Section8Data` with the index set `Set.Ici k₀`. -/
def Section8DataGen (n : ℕ) [NeZero n] (k₀ : ℕ) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) : Prop :=
  (∀ m : Set.Ici k₀,
      (basis (m, 1)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) ∧
  (∀ m : Set.Ici k₀,
      (basis (m, 3)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) ∧
  (∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
      S.F τ (samplePoint (n := n) (m.1 : ℝ)) = dirichletTerm m.1 τ) ∧
  (∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
      S.Ftilde τ (samplePoint (n := n) (m.1 : ℝ)) = 0) ∧
  (∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
      radialDeriv 1 (S.F τ) (samplePoint (n := n) (m.1 : ℝ))
        = (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ)) * dirichletTerm m.1 τ) ∧
  (∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
      radialDeriv 1 (S.Ftilde τ) (samplePoint (n := n) (m.1 : ℝ)) = 0)

/-! ## The paper's uniqueness input -/

/-- `g` is `o(e^{-2π c Im τ})` as `Im τ → ∞` in the strip `-1 ≤ Re τ ≤ 1` (uniformly in
`x`), which is the decay hypothesis of the paper's uniqueness lemma `lem:noPsolutions`
with `c = n₀ - 1`. -/
def TendsToZeroInStrip (n : ℕ) [NeZero n] (c : ℝ) (g : ℂ → E n → ℂ) : Prop :=
  ∀ x : E n, ∃ φ : ℝ → ℝ, Filter.Tendsto φ Filter.atTop (𝓝 0) ∧
    ∀ τ : ℂ, 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖g τ x‖ ≤ φ τ.im * Real.exp (-(2 * Real.pi * c * τ.im))

/-! ## Splitting the general-`k₀` Section 8 data -/

/-- `Work.FE.Section8DataGen` with the value normalisations only. -/
def Section8ValueDataGen (n : ℕ) [NeZero n] (k₀ : ℕ) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) : Prop :=
  (∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
      S.F τ (samplePoint (n := n) (m.1 : ℝ)) = dirichletTerm m.1 τ) ∧
  (∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
      S.Ftilde τ (samplePoint (n := n) (m.1 : ℝ)) = 0) ∧
  (∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
      radialDeriv 1 (S.F τ) (samplePoint (n := n) (m.1 : ℝ))
        = (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ)) * dirichletTerm m.1 τ) ∧
  (∀ (m : Set.Ici k₀) (τ : ℂ), 0 < τ.im →
      radialDeriv 1 (S.Ftilde τ) (samplePoint (n := n) (m.1 : ℝ)) = 0)

/-- `Work.FE.Section8DataGen` with the Fourier-transform relations only. -/
def Section8FourierDataGen (n : ℕ) [NeZero n] (k₀ : ℕ) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) : Prop :=
  (∀ m : Set.Ici k₀,
      (basis (m, 1)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) ∧
  (∀ m : Set.Ici k₀,
      (basis (m, 3)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1)

/-- The value half and the Fourier half give the general-`k₀` Section 8 data. -/
theorem section8DataGen_of {n : ℕ} [NeZero n] {k₀ : ℕ} {S : FunctionalEquationSolution n}
    {basis : SampleIdx k₀ → RSch n} (hv : Section8ValueDataGen n k₀ S basis)
    (hf : Section8FourierDataGen n k₀ S basis) : Section8DataGen n k₀ S basis := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  obtain ⟨h5, h6⟩ := hf
  exact ⟨h5, h6, h1, h2, h3, h4⟩

end Work.FE


end Work.CKFinal.Shadow
