import Mathlib
import Submission.Klingenberg
import Submission.Work.Final.DimOne.Defs
import Submission.Work.Final.DimOne.exists_ne_of_GExp_ray
import Submission.Work.Final.DimOne.period_of_GExp_ray_eq
import Submission.Work.Final.DimOne.continuous_rayLift
import Submission.Work.Final.DimOne.periods_bddBelow
import Submission.Work.Final.DimOne.exists_minimal_period
import Submission.Work.Final.DimOne.rayLift_injective
import Submission.Work.Final.DimOne.surjective_rayLift
import Submission.Work.Final.DimOne.not_simplyConnectedSpace_addCircle
import Submission.MetricScale

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dimension-one case of `KlingenbergBound`

`Submission.Klingenberg.KlingenbergBound cov` is stated for every bundle metric on `M`.  In the
odd-dimensional case the Klingenberg estimate is applied through
`Work.OddBound.diameter_gt_half_pi_odd_of_lt`, which requires `3 ≤ Module.finrank ℝ E`; the standing
hypothesis `Nontrivial E` only gives `1 ≤ finrank`.  The remaining case is `finrank ℝ E = 1`, i.e. a
**one-dimensional** manifold.

There the pinching hypotheses of `KlingenbergBound` are vacuous (a one-dimensional tangent space has
no orthonormal pair), so the statement is not a curvature statement at all: it says that a compact,
connected, simply connected, boundaryless one-dimensional manifold carries a pair of points at
distance `> π/2`.  That is a vacuous truth: there is **no** such manifold.  Indeed

* a unit-speed geodesic ray on a compact manifold is never injective
  (`Work.Final.DimOne.exists_ne_of_GExp_ray`), hence periodic
  (`Work.Final.DimOne.period_of_GExp_ray_eq`); since positive periods are bounded away from `0`
  (`Work.Final.DimOne.periods_bddBelow`) there is a *minimal* period
  (`Work.Final.DimOne.exists_minimal_period`), and the descent
  `Work.Final.rayLift : AddCircle P → M` of the ray is then a continuous bijection
  (`Work.Final.DimOne.rayLift_injective`, `Work.Final.DimOne.surjective_rayLift`,
  `Work.Final.DimOne.continuous_rayLift`);
* a continuous bijection from the compact circle onto the Hausdorff space `M` is a homeomorphism,
  so `M` is homeomorphic to `AddCircle P`, which transports simple connectivity to the circle —
  contradicting `Work.Final.DimOne.not_simplyConnectedSpace_addCircle`.

## Main result

* `Work.Final.false_of_finrank_one` — no compact, connected, simply connected, boundaryless
  one-dimensional Riemannian manifold with a metric-compatible torsion-free connection exists.
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

/-- **No compact, connected, simply connected, boundaryless one-dimensional manifold exists.**

(The statement is the dimension-one case of `Submission.Klingenberg.KlingenbergBound`: the curvature
hypotheses of that statement are vacuous in dimension one, and the conclusion "there is a pair of
points at distance `> π/2`" is empty because the manifold itself cannot exist.) -/
theorem false_of_finrank_one
    [I.Boundaryless] [CompactSpace M] [SimplyConnectedSpace M] [Nontrivial E]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim : Module.finrank ℝ E = 1) : False := by
  classical
  haveI : PathConnectedSpace M := inferInstance
  -- a point and a unit tangent vector
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  obtain ⟨p⟩ : Nonempty M := (inferInstance : Nonempty M)
  set u : TangentSpace I p := unitOf v hv with hudef
  have hu : ‖u‖ = 1 := unitOf_norm v hv
  have hu0 : u ≠ 0 := by rw [← norm_pos_iff, hu]; norm_num
  -- the ray self-intersects, hence is periodic
  obtain ⟨a, b, hab, heq⟩ :=
    Work.Final.DimOne.exists_ne_of_GExp_ray (I := I) (M := M) (cov := cov) hmet htor hdim p u hu
  obtain ⟨Q, hQpos, -, hQper⟩ :=
    Work.Final.DimOne.period_of_GExp_ray_eq (I := I) (M := M) (cov := cov) hmet hdim p u hu0 hab heq
  -- periods are bounded below, so there is a minimal one
  obtain ⟨ρ, hρpos, hρbd⟩ :=
    Work.Final.DimOne.periods_bddBelow (I := I) (M := M) (cov := cov) hmet htor p u hu
  obtain ⟨P, hPpos, hPper, hPmin⟩ :=
    Work.Final.DimOne.exists_minimal_period (I := I) (M := M) (cov := cov) hmet p u hu0
      ⟨Q, hQpos, hQper⟩ ⟨ρ, hρpos, hρbd⟩
  -- the descent to the circle is a continuous bijection
  have hcont := Work.Final.DimOne.continuous_rayLift (I := I) (M := M) (cov := cov)
    hmet p u hu0 hPpos hPper
  have hinj : Function.Injective (rayLift (cov := cov) hmet p u P hPper) :=
    Work.Final.DimOne.rayLift_injective (I := I) (M := M) (cov := cov) hmet p u hu (P := P)
      hPpos hPper hPmin
      (fun a b h1 h2 =>
        Work.Final.DimOne.period_of_GExp_ray_eq (I := I) (M := M) (cov := cov)
          hmet hdim p u hu0 h1 h2)
  have hsurj : Function.Surjective (rayLift (cov := cov) hmet p u P hPper) :=
    Work.Final.DimOne.surjective_rayLift (I := I) (M := M) (cov := cov) hmet htor hdim p u hu0
      hPpos hPper hcont
  -- hence a homeomorphism `AddCircle P ≃ₜ M`, transporting simple connectivity to the circle
  haveI : Fact (0 < P) := Fact.mk hPpos
  let e : AddCircle P ≃ M := Equiv.ofBijective (rayLift (cov := cov) hmet p u P hPper) ⟨hinj, hsurj⟩
  have hec : Continuous e := hcont
  have hhomeo : AddCircle P ≃ₜ M := Continuous.homeoOfEquivCompactToT2 hec
  have hsc : SimplyConnectedSpace (AddCircle P) :=
    (ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff hhomeo.toHomotopyEquiv).mpr
      (inferInstance : SimplyConnectedSpace M)
  exact Work.Final.DimOne.not_simplyConnectedSpace_addCircle hPpos hsc

end

end Work.Final
