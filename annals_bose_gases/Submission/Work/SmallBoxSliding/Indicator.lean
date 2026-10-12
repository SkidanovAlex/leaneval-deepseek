import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.Geom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The indicator-box layer of the sliding localisation

FS `eq:appsliding`'s sum over the boxes `B(u) = acube ℓ ∩ ((ℓd)•u + acube(ℓd))`
has an **exact** continuum form with the normalised box indicator

    boxInd ℓ d u x := 1_{x ∈ B(u)}(x)

(the exact continuum form of the lattice sum over the boxes; the
`u`-tube of a point has volume `1`, so no normalisation factor is needed).
In this layer the partition identities are literally
true — as opposed to the `χ_{B(u)}²`-weighted layer, where the `u`-integral is
the `δ`-like bump `χ_M(x/ℓ)²` (NOTES.md §7):

    (i)   `∫_u boxInd ℓ d u x du = 1_{x ∈ acube ℓ}`          (`boxInd_integral_u`)
    (ii)  `∫_u (∫_x boxInd ℓ d u x dx) du = ℓ³`             (`boxMass_integral_u`)
    (iii) `∫_u (Σ_{i,k} ∫_{abox} boxInd ℓ d u (x i)·(∂_{ik}Φ)²) du = kinWord N ℓ Φ`
                                                            (`kinWordBoxInd_integral_u`)
    (iv)  `∫_u (∫_x ρ x·boxInd ℓ d u x) du = ∫_{acube ℓ} ρ`
                                                            (`nBoxInd_integral_u`)

These are FS's `n = Σᵢ1_{B,i}` bookkeeping (`∫_u|B(u)|du = ℓ³`, the particle
number telescoping) in exact corpus form.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

/-- The **box indicator** `1_{B(u)}` as a function of both `u` and `x`. -/
noncomputable def boxInd (ℓ d : ℝ) (u x : ℝ³) : ℝ :=
  (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x

/-- The **true box volume** `|B(u)| = ∫_x 1_{B(u)}(x) dx` as a function of `u`. -/
noncomputable def boxMass (ℓ d : ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, boxInd ℓ d u x

end Work.SmallBoxSliding
