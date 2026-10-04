import Submission.Work.OddBound.longHomotopy.exists_lift_of_short

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The single-curve lifting lemma, under its original name

`Work.OddBound.longHomotopy.exists_lift_of_short_bis` is the name under which the single-curve form
of the lifting statement (a curve from `p` of length `< π/√K` lifts under `GExp p` to a continuous
curve in `T_pM` starting at `0`, with the norm bound `‖W s‖ ≤ curveLength h 0 s`) was first used; it
is the name consumed by `Work.OddBound.longHomotopy.lift_family_of_short`.  It is the same statement
as `Work.OddBound.longHomotopy.exists_lift_of_short`
(`Submission/Work/OddBound/longHomotopy/exists_lift_of_short.lean`); this module keeps both names
available.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius

namespace Work.OddBound.longHomotopy

theorem exists_lift_of_short_bis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {h : ℝ → M} {S : ℝ} (hS : 0 < S)
    (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (0 : ℝ) S)) (h0 : h 0 = p)
    (hlen : Submission.Length.curveLength (I := I) h 0 S < Real.pi / Real.sqrt K) :
    ∃ W : ℝ → TangentSpace I p, ContinuousOn W (Set.Icc (0 : ℝ) S) ∧ W 0 = 0 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S,
        Submission.GlobalExp.GExp (cov := cov) hmet p (W s) = h s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S, ‖W s‖ ≤ Submission.Length.curveLength (I := I) h 0 s) := exists_lift_of_short hmet htor hK hcurv hS hc h0 hlen

end Work.OddBound.longHomotopy
