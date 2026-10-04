import Mathlib
import Submission.Diff.Grad
import Submission.Diff.Interfaces
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared setup for the scalar maximum principle (`Work.Diff.GE.scalar_max_principle`)

This module collects the frozen contracts we build on (`Submission.Diff.Grad`,
`Submission.Diff.Interfaces`) together with the small facts about the *chosen* objects of
`Submission.Diff.Grad` that every later argument needs.  In particular it records the
specification of `smoothExt`, the `Classical.epsilon`-chosen smooth extension of a tangent
vector: `smoothExt x v` is a globally smooth vector field with `smoothExt x v x = v`.
Without this, nothing at all can be proved about `hessAt`, `covRm`, ... .
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

/-- **The specification of `smoothExt`**: the `Classical.epsilon`-chosen extension of a tangent
vector `v ∈ T_xM` is a globally smooth vector field whose value at `x` is `v`. -/
theorem smoothExt_spec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (x : M) (v : TangentSpace I x) :
    CMDiff ∞ (T% (smoothExt x v)) ∧ smoothExt x v x = v :=
  Classical.epsilon_spec (p := fun X : Π y : M, TangentSpace I y => CMDiff ∞ (T% X) ∧ X x = v)
    (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq v)

/-- The directional derivative of a smooth function along the smooth extension of `v` is smooth. -/
theorem contMDiff_mvfderiv_smoothExt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {u : M → ℝ} (hu : CMDiff ∞ u) (x : M) (v : TangentSpace I x) :
    CMDiff ∞ (fun y : M => mvfderiv I u y (smoothExt x v y)) :=
  Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hu (smoothExt_spec x v).1

end Work.Diff.GE
