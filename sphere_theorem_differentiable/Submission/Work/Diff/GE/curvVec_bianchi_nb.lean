import Mathlib
import Submission.Work.Diff.GE.bianchi_kato_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.GE Submission.CurvatureVec Submission.Curvature

/-- The first Bianchi identity for `curvVec`, with no `[I.Boundaryless]` hypothesis.
`Submission.CurvatureSym.curvVec_bianchi` states exactly the same conclusion, but carries a spurious
`[I.Boundaryless]` typeclass argument from its file's variable block; the files of the differentiable
sphere project cannot assume `I.Boundaryless`. Route: rewrite the three `curvVec`'s with
`Submission.CurvatureVec.curvVec_eq` (taking the smooth fields `smoothExt x u`, `smoothExt x v`,
`smoothExt x w`, specified by `Work.Diff.GE.smoothExt_spec`), then apply the field-level Bianchi
identity `Submission.Curvature.curv_bianchi`. Neither of those two assumes `I.Boundaryless`. -/
theorem curvVec_bianchi_nb
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (htor : cov.torsion = 0)
    (x : M) (u v w : TangentSpace I x) :
    curvVec cov x u v w + curvVec cov x v w u + curvVec cov x w u v = 0 := by
  obtain ⟨hX, hXx⟩ := smoothExt_spec (I := I) (M := M) x u
  obtain ⟨hY, hYx⟩ := smoothExt_spec (I := I) (M := M) x v
  obtain ⟨hZ, hZx⟩ := smoothExt_spec (I := I) (M := M) x w
  rw [curvVec_eq cov hcov hX hY hZ hXx hYx hZx,
    curvVec_eq cov hcov hY hZ hX hYx hZx hXx,
    curvVec_eq cov hcov hZ hX hY hZx hXx hYx]
  exact curv_bianchi cov hcov htor hX hY hZ

end Work.Diff.GE
