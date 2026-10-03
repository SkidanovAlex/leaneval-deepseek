/-
# The symbols of the §6 model approximation on `𝕋²` (Area A7)

The *pure* symbol definitions of `Work.KMTAreas.A7.smallKernelMass_le`: the double Fourier
coefficient `coeff` on `𝕋² = (ℝ/ℤ)²`, the discrete average symbol `avgSymb`, the two §6 symbols
`concSymb` (concrete kernel) and `modSymb`/`modSymbC` (model kernel), and the arithmetic symbol
`arithSymb`.

They are kept in this module — which imports only `A7/SmallDefs.lean` and
`A7/ModelApproxDefs.lean`, *not* `A7/SmallModApprox.lean` — so that the symbol algebra (in
particular the collapse identity `Σ₁ − Σ₂ = ∑_α Φ₁(θ₁-α₁)Φ₂(θ₂-α₂)·M0(α, ξ)`) can be developed
independently of the kernel definitions.  See `NOTES_A7_smallKernelMass_le.md` §1–§2.

**`modSymb` is WRONG** (`mTilde` is not `1`-periodic, so the `t`-integral of the modulated pieces
does not reduce to `mTilde` at the canonical representative); it is kept only because the existing
lemma `A7/concSymb_sub_modSymb_algebra.lean` is stated with it.  **The correct model symbol is
`modSymbC`** (the `t`-integral of `arithSymb · Ψ₁^t · Ψ₂^t`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallDefs
import Submission.Work.KMTAreas.A7.ModelApproxDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-- The double Fourier coefficient `∫_{θ₁}∫_{θ₂} F θ₁ θ₂ e(-a θ₁ - b θ₂)` of a function on
`𝕋² = (ℝ/ℤ)²`, with respect to the Haar (probability) measure.  The one-variable case is
`iwKernel F j = ∫_θ (fourier (-j) θ) · F θ`. -/
noncomputable def coeff (F : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) → ℂ) (a b : ℤ) : ℂ :=
  ∫ θ₁ : AddCircle (1 : ℝ),
    (∫ θ₂ : AddCircle (1 : ℝ), F θ₁ θ₂ * fourier (T := 1) (-a) θ₁ * fourier (T := 1) (-b) θ₂
      ∂AddCircle.haarAddCircle) ∂AddCircle.haarAddCircle

/-- The arithmetic symbol `avg` of (K1): the discrete average over the halved window,
as a function on `𝕋²`. -/
noncomputable def avgSymb (P : Polynomial ℤ) (N : ℕ) (θ₁ θ₂ : AddCircle (1 : ℝ)) : ℂ :=
  ((N : ℂ))⁻¹ * ∑ m ∈ Finset.Ioc (N / 2) N,
    fourier (T := 1) (m : ℤ) θ₁ * fourier (T := 1) (P.eval (m : ℤ)) θ₂

/-- The symbol `Σ₁ = Ψ₁·Ψ₂·avg` of the *concrete* kernel `smallKconc` (see (K1)). -/
noncomputable def concSymb (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ)
    (θ₁ θ₂ : AddCircle (1 : ℝ)) : ℂ :=
  iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiN N k₁)) θ₁
    * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeN P.natDegree N k₂)) θ₂
    * avgSymb P N θ₁ θ₂

/-- The arithmetic symbol `Arith` of (K1): `∑_{α} m_Ẑ(α) · periodize(m_*)(·-α)`. -/
noncomputable def arithSymb (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) (θ₁ θ₂ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
    mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
      * periodize (mStarF u) (θ₁ - α₁) * periodize (mStargF P.natDegree u) (θ₂ - α₂)

/-- The symbol `Σ₂ = Φ₁·Φ₂·m̃·Arith` of the *model* kernel `smallKmod` (see (K1)). -/
noncomputable def modSymb (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ)
    (θ₁ θ₂ : AddCircle (1 : ℝ)) : ℂ :=
  (∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂,
      periodize (varphiN N k₁) (θ₁ - β₁) * periodize (varphitildeN P.natDegree N k₂) (θ₂ - β₂)
        * mTilde P N ((AddCircle.equivIco (1 : ℝ) 0 (θ₁ - β₁)).val)
            ((AddCircle.equivIco (1 : ℝ) 0 (θ₂ - β₂)).val))
    * arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂

/-- **The corrected model symbol `Σ₂` of the §6 model operator** (see the "SESSION UPDATE"
block of the docstring above): the `t`-integral of the product of the arithmetic symbol
`Arith = arithSymb` with the two *modulated* exact-height Ionescu--Wainger symbols
`Ψ₁^t = iwSymbolSet A₁ (periodize φ^t)`, `Ψ₂^t = iwSymbolSet A₂ (periodize φ̃^t)`.  The
coefficients of `modSymbC` are `smallKmod` (this is the theorem `smallKmod_eq_coeff_modSymbC`
below, to be proved). -/
noncomputable def modSymbC (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ)
    (θ₁ θ₂ : AddCircle (1 : ℝ)) : ℂ :=
  ∫ t in (1/2 : ℝ)..1,
    arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
      * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
      * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂


/-- The `ℓ¹(ℤ²)`-mass of a bilinear kernel — *the same function* as the workspace's
`smKernMass` (`A7/SmallModApprox.lean`), kept here as well so that the spike-transfer lemma
`A7/smKernMass_coeff_spikeAt.lean` does not depend on that (currently less stable) module.  The
two definitions are syntactically identical, so `kernMassL1 K = smKernMass K` holds by `rfl`. -/
noncomputable def kernMassL1 (K : ℤ → ℤ → ℂ) : ℝ≥0∞ :=
  ∑' p : ℤ × ℤ, ‖K p.1 p.2‖ₑ

end

end Work.KMTAreas.A7
