import Submission.GeodesicLoop
import Submission.InjRadius
import Submission.InjSup

/-!
# Klingenberg's length bound in even dimensions: the transfer step

This file is the bottom of the subproject `Submission/Work/EvenBound` (namespace `Work.EvenBound`),
whose goal is Klingenberg's length bound in even dimensions:

> a compact, simply connected, **even-dimensional** Riemannian manifold with sectional curvature
> `K/4 ≤ sec ≤ K` (`0 < K`) has **every closed geodesic loop of length `≥ 2π/√K`**.

The mathematical content is the even-dimensional Klingenberg estimate on the **injectivity radius**
(`InjAllAtLeast hmet (π/√K)`), proved the classical way (no free-loop-space minimax): attain the
global injectivity radius `injSup`, glue the two minimal geodesics at the closest cut point (Xu's
Theorem B) into a closed geodesic of length `2 injSup`, shorten it by Synge's second-variation
argument, and contradict Xu's Theorem B with the resulting third minimal geodesic.

This module contains the **last step**: a geodesic loop of length `T` at `p` satisfies `2 r ≤ T`
for every `r` with `InjAtLeast hmet p r` (`Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast`),
so the uniform estimate `InjAllAtLeast hmet (π/√K)` gives `2π/√K ≤ T`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius

namespace Work.EvenBound

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **A geodesic loop of length `T` at `p` has `T ≥ 2π/√K` as soon as the exponential map is
injective up to `π/√K` uniformly.**

This is the transfer step `2 inj(p) ≤ T` (`Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast`)
applied to the uniform radius `π/√K`. -/
theorem length_bound_of_injAllAtLeast (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hinj : InjAllAtLeast hmet (Real.pi / Real.sqrt K))
    {p : M} {T : ℝ} {γ : ℝ → M}
    (hloop : Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ) :
    2 * Real.pi / Real.sqrt K ≤ T := by
  have h1 : 2 * (Real.pi / Real.sqrt K) ≤ T :=
    Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast (I := I) (cov := cov) hmet htor
      (Submission.GeodesicLoop.IsClosedGeodesicLoopAt.isGeodesicLoopAt (I := I) (cov := cov) hmet
        hloop)
      (Submission.InjRadius.injAtLeast_of_injAllAtLeast (I := I) hmet hinj p)
  calc 2 * Real.pi / Real.sqrt K = 2 * (Real.pi / Real.sqrt K) := by ring
    _ ≤ T := h1

end

end Work.EvenBound
