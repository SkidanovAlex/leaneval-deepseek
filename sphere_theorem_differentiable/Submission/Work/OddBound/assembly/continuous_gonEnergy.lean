import Mathlib
import Submission.Work.OddBound.PolygonModel
import Submission.Work.OddBound.polygonValue.balancing.continuousRiemannianDist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.assembly

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

/-!
# Continuity of the polygon energy

`gonEnergy p w = (N/2) · Σ_{i<N} d(v_i, v_{i+1})²` is a finite sum of squares of Riemannian
distances between consecutive vertices of the closed `N`-gon `w`, so its continuity in the
polygon `w : Fin (N-1) → M` reduces to

* continuity of the vertex map `w ↦ gonVert p w i` (a projection or a constant), and
* continuity of the Riemannian distance on `M × M`, which is
  `Work.OddBound.polygonValue.balancing.continuousRiemannianDist` (via Mathlib's continuous
  extended Riemannian distance, finiteness by connectedness, and `ENNReal.toReal`).

Both are unconditional in the hypotheses of the theorem: they only need a path-connected compact
Riemannian manifold with boundaryless model.
-/

/-- The `i`-th vertex of the closed `N`-gon is a continuous function of the polygon `w`: it is
either the base point `p` (for `i = 0` and for `i ≥ N`) or the projection `w ↦ w ⟨i-1, _⟩`. -/
theorem continuous_gonVert {M : Type*} [TopologicalSpace M] (p : M) {N : ℕ} (i : ℕ) :
    Continuous (fun w : Fin (N - 1) → M => Work.OddBound.gonVert p w i) := by
  by_cases h : i = 0 ∨ N ≤ i
  · have heq : (fun w : Fin (N - 1) → M => Work.OddBound.gonVert p w i)
        = fun _ : Fin (N - 1) → M => p := by
      funext w
      simp [Work.OddBound.gonVert, h]
    rw [heq]
    exact continuous_const
  · have heq : (fun w : Fin (N - 1) → M => Work.OddBound.gonVert p w i)
        = fun w : Fin (N - 1) → M => w ⟨i - 1, by omega⟩ := by
      funext w
      simp [Work.OddBound.gonVert, h]
    rw [heq]
    exact continuous_apply _

/-- The length of the `i`-th side of the polygon, `w ↦ d(v_i, v_{i+1})`, is continuous: it is the
composition of the continuous Riemannian distance on `M × M` with the continuous pair of vertex
maps. -/
theorem continuous_gonSideLen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    (p : M) {N : ℕ} (i : ℕ) :
    Continuous (fun w : Fin (N - 1) → M => Work.OddBound.gonSideLen (I := I) p w i) := by
  have hdist : Continuous (fun q : M × M => Submission.Distance.riemannianDist (I := I) q.1 q.2) :=
    Work.OddBound.polygonValue.balancing.continuousRiemannianDist (I := I)
  unfold Work.OddBound.gonSideLen
  exact hdist.comp ((continuous_gonVert p i).prodMk (continuous_gonVert p (i + 1)))

theorem continuous_gonEnergy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {N : ℕ} (p : M) :
    Continuous (fun w : Fin (N - 1) → M => Work.OddBound.gonEnergy (I := I) p w) := by
  have hsum : Continuous (fun w : Fin (N - 1) → M =>
      ∑ i : Fin N, (Work.OddBound.gonSideLen (I := I) p w i) ^ 2) := by
    refine continuous_finsetSum _ ?_
    intro i _
    exact (continuous_gonSideLen (I := I) p (i : ℕ)).pow 2
  unfold Work.OddBound.gonEnergy
  exact continuous_const.mul hsum

end Work.OddBound.assembly
