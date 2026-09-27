import Submission.Work.Mori.Defs
import Submission.Work.Mori.exists_isUnitGreenFunctionAt_of_isGreenFunctionAt

/-!
# Parabolicity from the absence of a unit Green function

The hypothesis `h` of the requested parabolic statement of uniformization is
`¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt z₀ E`: `X` carries no Green
function *with a normalised logarithmic pole*.  The classical normalisation of the pole coefficient
(`Work.Mori.exists_isUnitGreenFunctionAt_of_isGreenFunctionAt`) shows that any Green function can be
rescaled to a unit-pole one, so `h` is exactly the statement that `X` is **parabolic**:

* `Work.Mori.isParabolic_of_not_exists_isUnitGreenFunction` — `h` gives `Work.Parabolic.IsParabolic X`
  (this is what Mori's normal-form theorem is applied to);
* `Work.Mori.isParabolic_iff_not_exists_isUnitGreenFunction` — the equivalence for a non-compact `X`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

namespace Work.Mori

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Absence of a unit Green function is parabolicity.**  If `X` carries no unit-pole Green function
then it carries no Green function at all: a Green function in the relative-compactness sense can be
rescaled so that its pole coefficient is one
(`Work.Mori.exists_isUnitGreenFunctionAt_of_isGreenFunctionAt`). -/
theorem isParabolic_of_not_exists_isUnitGreenFunction (hX : ¬ CompactSpace X)
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) :
    Work.Parabolic.IsParabolic X := by
  rintro ⟨z₀, E, hE⟩
  obtain ⟨E', hE'⟩ := exists_isUnitGreenFunctionAt_of_isGreenFunctionAt hX hE
  exact h ⟨z₀, E', hE'⟩

/-- **Parabolicity is the absence of a unit Green function**, for a non-compact `X`.  The forward
direction is immediate (a unit Green function is a Green function); the backward direction is the
normalisation of the logarithmic pole. -/
theorem isParabolic_iff_not_exists_isUnitGreenFunction (hX : ¬ CompactSpace X) :
    Work.Parabolic.IsParabolic X ↔
      ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E := by
  constructor
  · rintro h ⟨z₀, E, hE⟩
    exact h ⟨z₀, E, hE.isGreenFunctionAt⟩
  · exact isParabolic_of_not_exists_isUnitGreenFunction hX

end Work.Mori
