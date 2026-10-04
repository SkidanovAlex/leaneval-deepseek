import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.rdist_continuous
import Submission.Work.Diff.C.rgrad_fcos
import Submission.Work.Diff.C.rhess_comp
import Submission.Work.Diff.C.ray_cos_compare
import Submission.GExpTwoSided
import Submission.GExpTranslate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Notation-free wrappers for the far-ball ("excess") development

The stated lemmas of this little chapter and the lemmas delegated for it are elaborated in files
that only get plain `import`s, so they may not use scoped notation (`∞`, `𝓘(·)`, `T%`).  This module
provides uniquely named abbreviations that stand for the scoped forms, in the style of
`Work.Diff.GE.scal_lapl_defs`.

* `SmoothAt f x`      --- `CMDiffAt ∞ f x` (for `f : M → ℝ`);
* `SmoothCurve γ`     --- `ContMDiff 𝓘(ℝ) I ∞ γ` (a `C^∞` curve `ℝ → M`);
* `GeodAt cov γ t`    --- `Submission.Geodesic.IsGeodesicAt cov γ t`;
* `vel γ t`           --- `Submission.Geodesic.curveVelocity (I := I) γ t`;
* `rayGExp hmet q u`  --- the `GExp`-ray `t ↦ GExp q (t • u)`.

Nothing here is a `sorry`; all definitions are transparent abbreviations.
-/

namespace Work.Diff.C

open Bundle
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- Notation-free form of `CMDiffAt ∞ f x` for a real-valued function on `M`. -/
abbrev SmoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : M → ℝ) (x : M) : Prop := CMDiffAt ∞ f x

/-- Notation-free form of `ContMDiff 𝓘(ℝ) I ∞ γ` for a curve `γ : ℝ → M`. -/
abbrev SmoothCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (γ : ℝ → M) : Prop := ContMDiff 𝓘(ℝ) I ∞ γ

/-- Notation-free form of `Submission.Geodesic.IsGeodesicAt cov γ t`. -/
abbrev GeodAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} (γ : ℝ → M) (t : ℝ) : Prop :=
  Submission.Geodesic.IsGeodesicAt cov γ t

/-- Notation-free form of the curve velocity `Submission.Geodesic.curveVelocity`. -/
noncomputable abbrev vel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  Submission.Geodesic.curveVelocity (I := I) γ t

/-- The `GExp`-ray `t ↦ GExp q (t • u)` of a tangent vector `u` at `q`. -/
noncomputable abbrev rayGExp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (q : M)
    (u : TangentSpace I q) : ℝ → M :=
  fun t => Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)

end Work.Diff.C
