import Mathlib
import Submission.Work.OddRadon.RadialDefs

/-!
# Auxiliary definitions for the `C¹` radial-system existence lemma

The data `A, B` of the radial system live on the closed interval `[0, π/2]` only (they are
arbitrary off it).  When the reconstructed radial functions `R, r` are built as
`α ↦ radialLocalInv n (2 + A α, B α)`, the *value* on `[0, π/2]` is determined by `A, B` there,
but the two-sided derivatives at the endpoints of the interval depend on the extension of the
data off the interval.  We therefore extend `A` (and `B`) by affine functions whose slopes are
the one-sided derivatives `derivWithin A (Icc 0 (π/2)) 0` and
`derivWithin A (Icc 0 (π/2)) (π/2)`, so that the extension is differentiable at the endpoints
with exactly those one-sided derivatives.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- Piecewise affine extension of a data function `A` off `[0, π/2]`: on `(-∞, 0]` the affine
function of slope `m0` through `(0, A 0)`, on `[0, π/2]` the function `A` itself, and on
`[π/2, ∞)` the affine function of slope `m1` through `(π/2, A (π/2))`. -/
noncomputable def radialDataExtend (A : ℝ → ℝ) (m0 m1 : ℝ) : ℝ → ℝ :=
  fun x => if x ≤ 0 then A 0 + m0 * x
    else if x ≤ Real.pi / 2 then A x
    else A (Real.pi / 2) + m1 * (x - Real.pi / 2)

/-- The extension of `A` whose slopes outside `[0, π/2]` are the one-sided derivatives of `A`
at the two endpoints. -/
noncomputable def radialExtensionOf (A : ℝ → ℝ) : ℝ → ℝ :=
  radialDataExtend A (derivWithin A (Set.Icc 0 (Real.pi / 2)) 0)
    (derivWithin A (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2))

/-- On `[0, π/2]` the extension agrees with the original data. -/
lemma radialDataExtend_eqOn (A : ℝ → ℝ) (m0 m1 : ℝ) :
    ∀ x ∈ Set.Icc 0 (Real.pi / 2), radialDataExtend A m0 m1 x = A x := by
  intro x hx
  by_cases h : x ≤ 0
  · have hx0 : x = 0 := le_antisymm h hx.1
    subst hx0
    simp [radialDataExtend]
  · rw [radialDataExtend, if_neg h, if_pos hx.2]

/-- On `[0, π/2]` the extension agrees with the original data. -/
lemma radialExtensionOf_eqOn (A : ℝ → ℝ) :
    ∀ x ∈ Set.Icc 0 (Real.pi / 2), radialExtensionOf A x = A x :=
  radialDataExtend_eqOn A _ _

end Work.OddRadon
