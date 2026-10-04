import Mathlib
import Submission.Work.OddBound.Defs

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

namespace Work.OddBound

theorem GExp_two_mul_eq_of_cutPointData
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : Submission.RauchK.CurvLe cov K) (hKpos : 0 < K)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hm : 0 < m) (hmπ : m < Real.pi / Real.sqrt K)
    (hinjp : InjAtLeast hmet p m) (hmaxp : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hξη : ξ ≠ η)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hminξ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ))
      = ENNReal.ofReal m)
    (hminη : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η))
      = ENNReal.ofReal m) :
    GExp (cov := cov) hmet p ((2 * m) • ξ) = p := by
  have hnc : ¬ Submission.ConjRadius.IsConjugateTime cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m :=
    Submission.ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt (cov := cov) hmet htor hK hKpos hmπ
  have hA : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m :=
    Submission.XuTrap.xuCornerExcluded (cov := cov) hmet htor p hm hinjp hmaxp ξ η hξ hη hξη
      hminξ hminη hmeet hnc
  exact Submission.GeodesicLoop.GExp_add_two_mul_of_velocity_eq_neg (cov := cov) hmet hξ hη hm hmeet hA

end Work.OddBound
