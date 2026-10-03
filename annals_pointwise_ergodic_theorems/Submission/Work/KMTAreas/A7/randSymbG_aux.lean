/-
# Vocabulary for `Work.KMTAreas.A7.randSymb_Tle_g_bound`

The `g`-side randomised cut-off of the `A7` small-scale assembly is the symbol

  `randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K
     = ∑_{n < K} ε n • (smallSymbG … (n+1) - smallSymbG … n)`,

a randomised *telescoping* sum of the modulated `g`-side bumps
`φ̃_{N,t}(ξ) = φ̃_N(ξ) e(P(Nt) ξ)` at the lacunary scales `N = ⌊a n⌋`.

This module collects the two pieces of vocabulary in which the analysis of that symbol is
phrased:

* `MikhlinBound ψ A` — the Mikhlin conditions `‖ψ‖ ≤ A`, `|ξ|‖ψ'‖ ≤ A`, `|ξ|²‖ψ''‖ ≤ A`; they are
  the hypothesis of the Mikhlin multiplier theorem
  (`Work.BourgainPlan.IonescuWainger.rescaled_mikhlin_multiplier_lp`), hence the source of the
  continuous `L^q(ℝ)`-multiplier bound `IsLqMultiplierBound q ψ M` which the Ionescu--Wainger
  multiplier theorem (area `A1`, `Work.KMTAreas.A7.IwLqGeneral`) consumes;

* `gProfile d k₂` and `gScale d N k₂` — the *profile* of the `g`-side bump: with
  `σ = gScale d N k₂ = 2^{d(Log N - k₂)}` one has
  `varphitildeN d N k₂ ξ = gProfile d k₂ (σ ξ)`, i.e. the bump is the rescaled fixed profile
  `gProfile`.  Two properties of the profile matter for the Mikhlin bounds:

  * `k₂ = 0`: `gProfile d 0 = η`, which is `1` on `[-1/2,1/2]` and `0` off `[-1,1]`;
  * `k₂ ≥ 1`: `gProfile d k₂ = η - η(2^d ·)`, which *vanishes* on `[-2^{-d-1},2^{-d-1}]` and is
    supported in `[-1,1]`; up to the factor `2^d` this is the mean-zero bump `ψ = η - η(2·)` of
    `Work.KMTAreas.A7.lacψ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs

set_option autoImplicit false

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

/-- **The Mikhlin conditions** for a symbol `ψ : ℝ → ℂ` with constant `A`:
`‖ψ‖ ≤ A`, `|ξ| ‖ψ'(ξ)‖ ≤ A` and `|ξ|² ‖ψ''(ξ)‖ ≤ A` pointwise.  These are exactly the three
hypotheses of the Mikhlin multiplier theorem
`Work.BourgainPlan.IonescuWainger.rescaled_mikhlin_multiplier_lp` (at scale `ε = 1` and shift
`c = 0`). -/
def MikhlinBound (ψ : ℝ → ℂ) (A : ℝ) : Prop :=
  0 ≤ A ∧ (∀ ξ : ℝ, ‖ψ ξ‖ ≤ A) ∧ (∀ ξ : ℝ, |ξ| * ‖deriv ψ ξ‖ ≤ A) ∧
    (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 ψ ξ‖ ≤ A)

/-- **The fixed frequency profile of the `g`-side bump.**  For `k₂ = 0` the bump
`φ̃_N(ξ) = η(2^{d Log N} ξ)` is the single rescaled cutoff; for `k₂ ≥ 1` it is the difference
`η(2^{d(Log N - k₂)} ξ) - η(2^{d(Log N - k₂) + d} ξ)`, which is the rescaled profile
`η - η(2^d ·)`. -/
def gProfile (d : ℕ) (k₂ : ℕ) : ℝ → ℂ :=
  if k₂ = 0 then Work.KMTContract.kmtEta
  else fun u : ℝ => Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta ((2 : ℝ) ^ d * u)

/-- **The frequency scale of the `g`-side bump at the scale `N`**: `σ = 2^{d (Log N - k₂)}`, so
that `φ̃_N(ξ) = gProfile d k₂ (σ ξ)`. -/
def gScale (d : ℕ) (N k₂ : ℕ) : ℝ := (2 : ℝ) ^ ((d : ℤ) * (logN N - (k₂ : ℤ)))

end

end Work.KMTAreas.A7
