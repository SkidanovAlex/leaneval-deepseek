import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The truncated distance and its supremum

`truncDist G F Υ t x = frobInfDist (rmC (G t) x) (F t ∩ frobBall (Υ t))` is the Frobenius distance
from the curvature of the metric `G t` at `x` to the truncated invariant family
`F t ∩ frobBall (Υ t)`, and `truncSup G F Υ t` is its supremum over the compact manifold `M`.
These are the two objects on which the time-regularity lemmas of Hamilton's maximum principle
(lower semicontinuity and right upper semicontinuity of `t ↦ truncSup …`) are stated.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.MP

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The Frobenius distance from the curvature of `G t` at `x` to the truncated family
`F t ∩ frobBall (Υ t)`. -/
noncomputable def truncDist (G : ℝ → SMet I M) (F : ℝ → Set (Curv4 (Module.finrank ℝ E)))
    (Υ : ℝ → ℝ) (t : ℝ) (x : M) : ℝ :=
  frobInfDist (rmC (G t) x) (F t ∩ frobBall (Υ t))

/-- Its supremum over the manifold. -/
noncomputable def truncSup (G : ℝ → SMet I M) (F : ℝ → Set (Curv4 (Module.finrank ℝ E)))
    (Υ : ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup ((truncDist G F Υ t) '' Set.univ)

end Work.Diff.MP
