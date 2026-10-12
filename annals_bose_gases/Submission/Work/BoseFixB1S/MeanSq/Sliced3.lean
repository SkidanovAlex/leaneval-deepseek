import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.MeanSq.Box3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1S

/-!
# The three nested one-dimensional sliced averages

This file contains the three auxiliary functions that turn the *three-dimensional* box average
`(∫_{y ∈ slBox ℓ h u} F y) / |slBox ℓ h u|` into an iterated *one-dimensional* sliced average, so
that the one-dimensional mean-square bound `Work.BoseFixB1S.meanSq1d` can be applied coordinate by
coordinate.

The three levels are (all volumes are the Lebesgue volumes of the one-dimensional sliding
intervals `slI ℓ h t`):

* `slS ℓ h F c y₀ y₁ = (1/|slI c|) * ∫_{y₂ ∈ slI c} F ![y₀,y₁,y₂]` — the innermost level, whose
  free integration variable is the third coordinate `c`;
* `slR ℓ h F b c y₀ = (1/|slI b|) * ∫_{y₁ ∈ slI b} slS ℓ h F c y₀ y₁` — the middle level, whose
  free integration variable is `b`, with `(c, y₀)` frozen;
* `slN ℓ h F a b c = (1/|slI a|) * ∫_{y₀ ∈ slI a} slR ℓ h F b c y₀` — the outer level, whose free
  integration variable is `a`, with `(b,c)` frozen.

So `slN ℓ h F a b c` is the fully nested normalised average, and the pointwise identity
`(∫_{y ∈ slBox ℓ h u} F y)/|slBox ℓ h u| = slN ℓ h F (u 0) (u 1) (u 2)` is the "peeling step".
-/

/-- The innermost sliced average: normalised average of `F ![y₀,y₁,·]` over the sliding interval
`slI ℓ h c` of the third coordinate. -/
noncomputable def slS (ℓ h : ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) (c y₀ y₁ : ℝ) : ℝ≥0∞ :=
  (volume (slI ℓ h c))⁻¹ * ∫⁻ y₂ in slI ℓ h c, F ![y₀, y₁, y₂]

/-- The middle sliced average: normalised average of `slS ℓ h F c y₀ ·` over the sliding interval
`slI ℓ h b` of the second coordinate. -/
noncomputable def slR (ℓ h : ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) (b c y₀ : ℝ) : ℝ≥0∞ :=
  (volume (slI ℓ h b))⁻¹ * ∫⁻ y₁ in slI ℓ h b, slS ℓ h F c y₀ y₁

/-- The outer sliced average: normalised average of `slR ℓ h F b c ·` over the sliding interval
`slI ℓ h a` of the first coordinate. -/
noncomputable def slN (ℓ h : ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) (a b c : ℝ) : ℝ≥0∞ :=
  (volume (slI ℓ h a))⁻¹ * ∫⁻ y₀ in slI ℓ h a, slR ℓ h F b c y₀

end Work.BoseFixB1S
