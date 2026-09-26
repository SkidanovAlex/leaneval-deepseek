import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.Main

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

/-- **The missing bridge, Step 1--2 and Section 8.**  Every well-behaved solution of the
functional equations (hypotheses (i)--(v) of Theorem 3.1) extends to an
`InterpolationSolution`, i.e. carries

* the two Fourier expansions of Steps 1--2 with radial Schwartz coefficients,
* the termwise radial differentiability of those expansions,
* polynomial growth of the radial and Schwartz seminorms of the coefficients,
* the Section 8 normalisations at the sample radii and the Fourier-transform relations
  `ã = â`, `b̃ = b̂`.

NOT PROVED here.  Steps 1--2 are analytic (the first half of them is
`Work.FunctionalEquations.DirichletExpansion` together with
`Work.FunctionalEquations.ExpansionFromFunctionalEquations`, which give the expansion at
one `x` at a time); the Section 8 inputs require the uniqueness lemma `lem:noPsolutions`
of the paper and the modular-forms construction of `F`. -/
def ExpansionDataExists (n : ℕ) [NeZero n] : Prop :=
  ∀ S : FunctionalEquationSolution n, ∃ I : InterpolationSolution n,
    I.toFunctionalEquationSolution = S

/-- **The literal form of the requested statement, with hypotheses (i)--(v) only.**  Every
solution of the functional equations would already yield `Work.Core.InterpolationBasis n 1`.

NOT PROVED, and believed to be false for general `n`: the `delta` field is equivalent to
surjectivity of the sampling map restricted to the radial Schwartz space, which holds in
dimensions `8` and `24` at the sample radii `√(2m)`, `m ≥ 1` (respectively `m ≥ 2`), but
is not implied by (i)--(v).  See the module documentation. -/
def FunctionalEquationsAloneSuffice (n : ℕ) [NeZero n] : Prop :=
  ∀ S : FunctionalEquationSolution n, Nonempty (Work.Core.InterpolationBasis n 1)

/-- The main theorem converts the missing bridge into the literal form: if every solution
of the functional equations carries the Theorem 3.1 and Section 8 data, then hypotheses
(i)--(v) alone suffice. -/
theorem functionalEquationsAloneSuffice_of_expansionDataExists (n : ℕ) [NeZero n]
    (h : ExpansionDataExists n) : FunctionalEquationsAloneSuffice n :=
  fun S => ⟨interpolationBasis_of_functionalEquations n (h S).choose⟩


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

/-- The analytic half and the Section 8 half together give `ExpansionDataExists`. -/
theorem expansionDataExists_of {n : ℕ} [NeZero n]
    (hA : ∀ S : FunctionalEquationSolution n, ∃ basis : SampleIdx 1 → RSch n,
      ExpansionData n S basis)
    (hB : ∀ (S : FunctionalEquationSolution n) (basis : SampleIdx 1 → RSch n),
      ExpansionData n S basis → Section8Data n S basis) :
    ExpansionDataExists n := by
  intro S
  obtain ⟨basis, hF, hFt, hD, hDt, hG⟩ := hA S
  obtain ⟨hfb, hfb', hvF, hvFt, hvdF, hvdFt⟩ := hB S basis ⟨hF, hFt, hD, hDt, hG⟩
  exact ⟨{ toFunctionalEquationSolution := S
           basis := basis
           expansion_F := hF
           expansion_Ftilde := hFt
           expansion_F_radialDeriv := hD
           expansion_Ftilde_radialDeriv := hDt
           fourier_basis := hfb
           fourier_basis' := hfb'
           value_F := hvF
           value_Ftilde := hvFt
           value_radialDeriv_F := hvdF
           value_radialDeriv_Ftilde := hvdFt
           growth_radial := hG }, rfl⟩


/-- **The value half of the Section 8 data.**  The normalisations of `F`, `F̃` and of their
radial derivatives at the sample radii.  For the concrete construction these follow from
the vanishing to second order of the prefactor `4 sin²(πr²/2)` of the kernel at
`r = √(2m)`: see `Work.FunctionalEquations.KernelSampleValues` and
`Work.FunctionalEquations.KernelSampleDerivValues`. -/
def Section8ValueData (n : ℕ) [NeZero n] (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) : Prop :=
  (∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
      S.F τ (samplePoint (n := n) (m.1 : ℝ)) = dirichletTerm m.1 τ) ∧
  (∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
      S.Ftilde τ (samplePoint (n := n) (m.1 : ℝ)) = 0) ∧
  (∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
      radialDeriv 1 (S.F τ) (samplePoint (n := n) (m.1 : ℝ))
        = (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ)) * dirichletTerm m.1 τ) ∧
  (∀ (m : Set.Ici (1 : ℕ)) (τ : ℂ), 0 < τ.im →
      radialDeriv 1 (S.Ftilde τ) (samplePoint (n := n) (m.1 : ℝ)) = 0)

/-- **The Fourier-transform half of the Section 8 data**, `ã = â` and `b̃ = b̂`.  This is
the input for which the paper invokes the uniqueness lemma `lem:noPsolutions` (Section 8:
applying `𝓕_x` and `τ ↦ -1/τ` to the three functional equations shows that so is
`(𝓕_x F̃, 𝓕_x F)`, and the difference of the two solutions satisfies the homogeneous
system, so it vanishes in dimensions `8` and `24`). -/
def Section8FourierData (n : ℕ) [NeZero n] (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) : Prop :=
  (∀ m : Set.Ici (1 : ℕ),
      (basis (m, 1)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) ∧
  (∀ m : Set.Ici (1 : ℕ),
      (basis (m, 3)).1 = FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1)

/-- The value half and the Fourier-transform half of the Section 8 data together give the
Section 8 data. -/
theorem section8Data_of {n : ℕ} [NeZero n] {S : FunctionalEquationSolution n}
    {basis : SampleIdx 1 → RSch n} (hv : Section8ValueData n S basis)
    (hf : Section8FourierData n S basis) : Section8Data n S basis := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  obtain ⟨h5, h6⟩ := hf
  exact ⟨h5, h6, h1, h2, h3, h4⟩


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

/-- **The uniqueness input of Section 8 (paper `lem:noPsolutions`).**  Every solution of the
*homogeneous* functional equations that decays like `o(e^{-2π c Im τ})` in the strip
`-1 ≤ Re τ ≤ 1` vanishes identically.

For `c = 0` this is the statement the paper proves at weight `4` (dimension `8`), and for
`c = 1` at weight `12` (dimension `24`); it is the only input of this area that is not
derived from hypotheses (i)--(v).  See `Work.FE.section8Data_of_rigidity`, which turns it
into the Section 8 data, and `Work.FE.interpolationBasis_of_functionalEquations_of_rigidity`,
which turns it into the interpolation basis. -/
def HomogeneousRigidity (n : ℕ) [NeZero n] (c : ℝ) : Prop :=
  ∀ (g gt : ℂ → E n → ℂ),
    (∀ x, DifferentiableOn ℂ (fun τ : ℂ => g τ x) {τ : ℂ | 0 < τ.im}) →
    (∀ x, DifferentiableOn ℂ (fun τ : ℂ => gt τ x) {τ : ℂ | 0 < τ.im}) →
    (∀ (τ : ℂ) (x : E n), 0 < τ.im → g (τ + 2) x - 2 * g (τ + 1) x + g τ x = 0) →
    (∀ (τ : ℂ) (x : E n), 0 < τ.im → gt (τ + 2) x - 2 * gt (τ + 1) x + gt τ x = 0) →
    (∀ (τ : ℂ) (x : E n), 0 < τ.im → g τ x + slashFactor n τ * gt (-1 / τ) x = 0) →
    TendsToZeroInStrip n c g → TendsToZeroInStrip n c gt →
    ∀ (τ : ℂ) (x : E n), 0 < τ.im → g τ x = 0 ∧ gt τ x = 0


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
