import Mathlib
import Submission.Work.OddBound.Defs
import Submission.BrokenLength

namespace Work.OddBound

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

/-- **The `GExp`-ray of a unit vector has unit speed *everywhere*, including at `0`.**  The library
lemma `Submission.ConjEnergy.curveSpeed_ray` requires a non-zero parameter (`∀ s ≠ 0`), which is not
enough for the hypotheses of `Work.OddBound.HasRotatingFieldInput` (they quantify over the closed
interval `Icc 0 L`); at `t = 0` the claim follows from
`Submission.GExpVelocity.curveVelocity_GExp_smul_zero`.
Note: `Submission.BrokenLength.curveSpeed_GExp_ray` already gives `curveSpeed γ t = ‖ξ‖` for *every*
`t` (it is not in the import closure of the proposed header, but may be imported). -/
theorem curveSpeed_GExp_ray_eq_one (hmet : IsMetricCompatible cov)
    {p : M} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) :
    ∀ t : ℝ, curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t = 1 := by
  -- A unit vector is non-zero, so the `BrokenLength` speed computation applies.
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  -- `curveSpeed_GExp_ray` holds at *every* time `t` (the case `t = 0` being part of it),
  -- and says the speed is constantly `‖ξ‖ = 1`.
  intro t
  rw [Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hξne t, hξ]

end Work.OddBound
