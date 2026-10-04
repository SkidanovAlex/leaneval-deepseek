import Submission.Work.OddBound.Defs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.OddBound

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The transfer step: the injectivity bound implies the length bound.**  A closed geodesic loop of
length `T` at `p` satisfies `2 inj(p) ≤ T`
(`Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast`), so `π/√K ≤ m` together with
`InjAtLeast hmet p m` gives `2π/√K ≤ T`.

This is the last step of the odd-dimensional Klingenberg estimate, and mirrors
`Work.EvenBound.length_bound_of_injAllAtLeast` (the uniform form): once the injectivity estimate
`InjAllAtLeast hmet (π/√K)` is available, the length bound follows immediately. -/
theorem two_pi_div_sqrt_le_of_inj
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K)
    {p : M} {T : ℝ} {γ : ℝ → M} {m : ℝ}
    (hloop : Submission.KlingenbergLemma.IsClosedGeodesicLoopAt (I := I) hmet p T γ)
    (hinj : InjAtLeast hmet p m) (hm : Real.pi / Real.sqrt K ≤ m) :
    2 * Real.pi / Real.sqrt K ≤ T := by
  have h1 : 2 * m ≤ T :=
    Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast (I := I) (cov := cov) hmet htor
      (Submission.GeodesicLoop.IsClosedGeodesicLoopAt.isGeodesicLoopAt (I := I) (cov := cov) hmet
        hloop) hinj
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  rw [show 2 * Real.pi / Real.sqrt K = 2 * (Real.pi / Real.sqrt K) from by ring]
  calc 2 * (Real.pi / Real.sqrt K) ≤ 2 * m := by nlinarith [hm]
    _ ≤ T := h1


end Work.OddBound
