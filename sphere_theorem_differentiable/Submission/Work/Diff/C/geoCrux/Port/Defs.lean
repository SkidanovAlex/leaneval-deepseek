import Mathlib
import Submission.JacobiGlobal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Delegation wrappers for the two-centre core (`Work.Diff.C.geoCrux.twoCentre_core`)

This module collects, as closed `abbrev`s, the statements of the pieces that the proof of
`Work.Diff.C.geoCrux.Port.TwoCentreCoreProp` (`Submission/Work/Diff/C/geoCrux/twoCentre_core.lean`) needs
as inputs, so that they can be delegated: the delegation harness elaborates a submitted statement in
a file that contains only the `depends_on` imports and **no `open` commands**, and in that bare
context the Riemannian-bundle binders (`TangentSpace`, `RiemannianBundle`, …) do not elaborate.

## `JacobiUniqCoreProp`

Uniqueness of Jacobi fields with prescribed value and covariant derivative at one time, for a
`C^∞` curve with nowhere vanishing velocity.  This is the statement of
`Submission.Work.Diff.C.isJacobiAt_eq_of_data` (which is a `sorry` in the workspace), phrased as a
closed `Prop` so that it is delegable; it is the tool that identifies a Jacobi field with the field
constructed from its data in the two-centre argument.

The context is the same as that of the two-centre core: a `C^∞` Riemannian bundle with `IsManifold I
∞ M` (smooth, not analytic — the workspace copy uses the analytic level).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux.Port

/-- **Uniqueness of Jacobi fields with prescribed data at one time.**  Two Jacobi fields along the
same `C^∞` curve with nowhere vanishing velocity which have the same value and the same covariant
derivative at one time are equal everywhere. -/
abbrev JacobiUniqCoreProp : Prop :=
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

end Work.Diff.C.geoCrux.Port
