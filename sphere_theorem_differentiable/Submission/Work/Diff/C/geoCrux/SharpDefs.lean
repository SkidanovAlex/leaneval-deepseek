import Mathlib
import Submission.Work.Diff.C.geoCrux.RadialLib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions and interfaces for the sharp radial modulus bound

This module collects the *closed* interfaces (`Prop`-valued `abbrev`s, so that they can be
delegated in the bare context of a delegated statement) used by the proof of
`Work.Diff.C.geoCrux.radial_modulus_sharp`.

The two geometric inputs that are proved elsewhere in the fleet are:

* `RayMinProp` — the ray from any point is minimising up to `π - arccos (1-c)`.  This is
  `Work.Diff.C.geoCrux.ray_minimising_upto` (`Submission/Work/Diff/C/geoCrux/injectivity_radius.lean`)
  **without** its (unused! it is only passed to `rdist_smooth_eikonal`, whose proof does not use it)
  `hdiam` hypothesis.
* `JacobiUniqProp` — the uniqueness of the Jacobi equation from initial data at a point
  (`Submission/Work/Diff/C/isJacobiAt_eq_of_data.lean`, whose statement carries the detailed route).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux

/-- **Uniqueness of Jacobi fields with prescribed data at one time** (smooth level, own copy so
that the development does not depend on a file that is being edited elsewhere). -/
abbrev JacobiUniqSmooth : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞ γ)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {J Z : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hZ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ Z t)
    {t₀ : ℝ} (hv : J t₀ = Z t₀)
    (hd : Submission.JacobiGlobal.covAlong cov J t₀ = Submission.JacobiGlobal.covAlong cov Z t₀),
    ∀ t : ℝ, J t = Z t

end Work.Diff.C.geoCrux
