import Mathlib
import Submission.Klingenberg
import Submission.GlobalExp
import Submission.GExpRayZero
import Submission.GExpTwoSided
import Submission.GExpVelocity
import Submission.HopfRinow
import Submission.MetricScale

/-!
# Dimension one: the periodic `GExp`-ray and its lift to `AddCircle`

In dimension one a unit-speed geodesic of a compact manifold is never injective
(`Work.Final.exists_ne_of_GExp_ray`) and hence is periodic
(`Work.Final.period_of_GExp_ray_eq`).  A periodic ray `s ↦ GExp p (s • u)` with period `P > 0`
descends to the circle: this file defines that descent (`Work.Final.rayLift`) and its basic
evaluation lemma.

The circle obtained is the whole of `M` (`Work.Final.surjective_rayLift`), the descent is a
covering map (`Work.Final.isCoveringMap_rayLift`), and a covering map over a simply connected base
is injective (`Work.Final.injective_of_isCoveringMap_of_simplyConnected`); a cover of the circle is
therefore a homeomorphism, which contradicts `Work.Final.not_simplyConnectedSpace_addCircle`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.CurvatureVec

namespace Work.Final

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- The unit-speed ray `s ↦ GExp p (s • u)` is periodic of period `P` — the hypothesis form used
throughout this directory. -/
lemma periodic_rayGExp (hmet : IsMetricCompatible cov) (p : M) (u : TangentSpace I p) (P : ℝ)
    (hper : ∀ s : ℝ, GExp (cov := cov) hmet p ((s + P) • u) = GExp (cov := cov) hmet p (s • u)) :
    Function.Periodic (fun s : ℝ ↦ GExp (cov := cov) hmet p (s • u)) P :=
  hper

/-- **The descent of a periodic `GExp`-ray to the circle `AddCircle P`.**  If the ray
`s ↦ GExp p (s • u)` has period `P`, it factors through `ℝ ⧸ ℤ ∙ P`. -/
noncomputable def rayLift (hmet : IsMetricCompatible cov) (p : M) (u : TangentSpace I p) (P : ℝ)
    (hper : ∀ s : ℝ, GExp (cov := cov) hmet p ((s + P) • u) = GExp (cov := cov) hmet p (s • u)) :
    AddCircle P → M :=
  Function.Periodic.lift (periodic_rayGExp (cov := cov) hmet p u P hper)

/-- Evaluation of the descent at a representative: `rayLift` is the ray. -/
@[simp] lemma rayLift_coe (hmet : IsMetricCompatible cov) (p : M) (u : TangentSpace I p) (P : ℝ)
    (hper : ∀ s : ℝ, GExp (cov := cov) hmet p ((s + P) • u) = GExp (cov := cov) hmet p (s • u))
    (x : ℝ) :
    rayLift (cov := cov) hmet p u P hper (x : AddCircle P) = GExp (cov := cov) hmet p (x • u) :=
  Function.Periodic.lift_coe _ x

end

end Work.Final
