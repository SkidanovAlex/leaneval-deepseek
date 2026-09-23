import Mathlib
import Submission.GExpJointPt
import Submission.Work.OddBound.LiftKit

namespace Work.OddBound.pvCrux

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.GlobalExp Submission.Length Submission.InjRadius

/-- **Joint continuity of the global exponential map in a fixed chart**, along a countably
generated filter: if `q t → p` and the chart coordinates `a t` of the velocity converge to `a₀`,
then `GExp (q t) (frameVector z₀ (q t) (a t)) → GExp p (frameVector z₀ p a₀)`.

The filter version reduces to the sequence version
(`Submission.GExpJointPt.tendsto_GExp_frameVector`) by `Filter.tendsto_iff_seq_tendsto`, which
applies because `l` is countably generated. -/
theorem gExp_joint_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {z₀ : M} {p : M} (hp : p ∈ (chartAt H z₀).source)
    {q : α → M} {a : α → E} {a₀ : E}
    (hq : Filter.Tendsto q l (𝓝 p)) (ha : Filter.Tendsto a l (𝓝 a₀)) :
    Filter.Tendsto (fun t => Submission.GlobalExp.GExp (cov := cov) hmet (q t)
        (Submission.Geodesic.frameVector (I := I) z₀ (q t) (a t)))
      l (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet p
        (Submission.Geodesic.frameVector (I := I) z₀ p a₀))) := by
  refine Filter.tendsto_iff_seq_tendsto.2 fun u hu => ?_
  simpa only [Function.comp_def] using
    Submission.GExpJointPt.tendsto_GExp_frameVector (cov := cov) hmet htor hp
      (hq.comp hu) (ha.comp hu)

end Work.OddBound.pvCrux
