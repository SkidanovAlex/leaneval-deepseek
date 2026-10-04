import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Notation-free wrappers for the `scal_lapl` development

The stated lemmas of this little chapter (`scal_lapl.lean`) and the lemmas delegated for it are
elaborated in files that only get plain `import`s, so they may not use scoped notation (`T%`, `∞`).
This module provides uniquely named abbreviations (`SmoothSect`, `SmoothScal`) that stand for the
scoped forms, exactly as `Work.Diff.Evol.LapKit` does for the `Evol` area.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The section `X : Π y, T_yM` is `C^∞` (notation-free form of `CMDiff ∞ (T% X)`). -/
abbrev SmoothSect (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (X : Π y : M, TangentSpace I y) : Prop :=
  CMDiff ∞ (T% X)

/-- The function `u : M → ℝ` is `C^∞` (notation-free form of `CMDiff ∞ u`). -/
abbrev SmoothScal (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (u : M → ℝ) : Prop := CMDiff ∞ u

end Work.Diff.GE
