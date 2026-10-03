/-
# The spike objects of the §6 model approximation (Area A7)

This module fixes the two objects into which the §6 collapse decomposes the symbol difference
`concSymb - modSymbC` (see `A7/smallKernelMass_le.lean`, step (K2)):

* `bumpSymb P k₁ k₂ N β₁ β₂ θ` — the *spike bump*: the product of the two periodised (narrow)
  §6 bumps centred at the arithmetic frequency pair `β = (β₁,β₂)`;

* `spikeSymb ρ P l₁ l₂ k₁ k₂ N β₁ β₂ θ` — the *spike symbol*: the spike bump times the §6
  symbol difference `M0 P N q β₁ β₂` evaluated at the canonical lifts of `θ - β`
  (`q = arithQ ρ (max l₁ l₂)`);

* `spikeProfile P N k₁ k₂ q β₁ β₂` — the corresponding *real profile*
  `(x₁,x₂) ↦ φ_N(x₁) φ̃_N(x₂) M0 P N q β₁ β₂ x₁ x₂` on `ℝ²`, whose `ℝ²`-Fourier coefficients
  are (up to the unimodular factors `fourier(-a)β₁ fourier(-b)β₂`) the coefficients of the spike
  symbol (`coeff_spike`), and to which the `ℓ¹(ℤ²)`-Fourier-mass bound `mass_fourier_le`
  applies.

Keeping them here (in a module that only imports the *definition* modules) lets the
per-spike analytic estimate be stated and proved independently of the symbol algebra.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.symbolDefs
import Submission.Work.KMTAreas.A7.liftCollapse

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- The *bump* of the spike at the arithmetic frequency pair `(β₁,β₂)`: the product of the two
periodised narrow bumps `φ_N = varphiN N k₁`, `φ̃_N = varphitildeN d N k₂` shifted by `β`. -/
noncomputable def bumpSymb (P : Polynomial ℤ) (k₁ k₂ N : ℕ)
    (β₁ β₂ : Work.Analysis.IonescuWainger.Circle)
    (θ₁ θ₂ : Work.Analysis.IonescuWainger.Circle) : ℂ :=
  periodize (varphiN N k₁) (θ₁ - β₁) * periodize (varphitildeN P.natDegree N k₂) (θ₂ - β₂)

/-- The real *profile* of the spike at the arithmetic frequency pair `(β₁,β₂)` and the modulus
`q`: `(x₁,x₂) ↦ φ_N(x₁) φ̃_N(x₂) M0 P N q β₁ β₂ x₁ x₂`. -/
noncomputable def spikeProfile (P : Polynomial ℤ) (N k₁ k₂ q : ℕ)
    (β₁ β₂ : Work.Analysis.IonescuWainger.Circle) (x₁ x₂ : ℝ) : ℂ :=
  varphiN N k₁ x₁ * varphitildeN P.natDegree N k₂ x₂ * M0 P N q β₁ β₂ x₁ x₂

/-- The *spike symbol* of the §6 collapse: the spike bump times the symbol difference `M0`
evaluated at the canonical lifts of `θ - β`. -/
noncomputable def spikeSymb (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ)
    (β₁ β₂ : Work.Analysis.IonescuWainger.Circle)
    (θ₁ θ₂ : Work.Analysis.IonescuWainger.Circle) : ℂ :=
  bumpSymb P k₁ k₂ N β₁ β₂ θ₁ θ₂
    * M0 P N (arithQ ρ (max l₁ l₂)) β₁ β₂
        (lift (θ₁ - β₁)) (lift (θ₂ - β₂))

/-- The *mean-value spike* at `(β₁,β₂)`: the spike bump times the oscillatory integral
`mTilde` at the canonical lifts of `θ - β`.  This is the object that the `t`-integral of the two
modulated Ionescu--Wainger symbols produces. -/
noncomputable def meanSpike (P : Polynomial ℤ) (k₁ k₂ N : ℕ)
    (β₁ β₂ : Work.Analysis.IonescuWainger.Circle)
    (θ₁ θ₂ : Work.Analysis.IonescuWainger.Circle) : ℂ :=
  bumpSymb P k₁ k₂ N β₁ β₂ θ₁ θ₂ * mTilde P N (lift (θ₁ - β₁)) (lift (θ₂ - β₂))

end

end Work.KMTAreas.A7
