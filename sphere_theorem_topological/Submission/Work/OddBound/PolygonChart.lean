import Submission.Work.OddBound.PolygonModel

/-!
# The critical-point and index vocabulary on the polygon model

This module fixes the interface between the three remaining pieces of
`Work.OddBound.MinimaxExtraction` (see `refs/NOTES.md` §14):

* the **mountain pass** on the polygon space `P = Fin (N-1) → M`
  (`Work.OddBound.mountainPass.exists_critical_index_le_one_manifold`);
* the **first variation** (`Work.OddBound.polygon.isCritical_gonEnergy_geodesic`), which turns a
  critical polygon into a closed geodesic;
* the **index transfer** (`Work.OddBound.indexTransfer.hasNegDefPlane_of_not_dirichletIndexLeOne`),
  which turns a negative-definite Dirichlet plane along that geodesic into a negative-definite
  2-plane for the Hessian of `gonEnergy` at the critical polygon.

## Conventions

A **chart-based critical point** of a real function `f` on a charted space `P` is a point `z` such
that *some* chart of the atlas has vanishing coordinate derivative at `e z` (`IsCriticalChart`).
A **negative-definite plane** at `z` is a two-dimensional subspace on which *some* chart's second
coordinate derivative is negative definite (`HasNegDefPlane`).  Both notions are chart-independent
on a `C²` manifold, which is exactly the content of the chart-change lemmas
(`IsCriticalChart.chart_independent`, `HasNegDefPlane.chart_independent`); the chart-change
comparison for a *critical* point needs no information beyond `C²`-compatibility of the charts,
because the first-order correction term vanishes there.
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
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

noncomputable section

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

/-! ## 1. Critical points and negative-definite planes, chart-based -/

/-- **`f` is critical at `z`** if some chart of the atlas has vanishing coordinate derivative at
`e z`.  On a `C²` charted space this is chart-independent. -/
def IsCriticalChart (H' : Type*) [TopologicalSpace H'] [NormedAddCommGroup H']
    [NormedSpace ℝ H'] {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] (f : P → ℝ)
    (z : P) : Prop :=
  ∃ (e : OpenPartialHomeomorph P H') (_ : e ∈ atlas H' P) (_ : z ∈ e.source),
    fderiv ℝ (fun x : H' => f (e.symm x)) (e z) = 0

/-- **`f` has a negative-definite plane at `z`** if some chart of the atlas has a two-dimensional
subspace on which the second coordinate derivative is negative definite.  On a `C²` charted space
this is chart-independent. -/
def HasNegDefPlane (H' : Type*) [TopologicalSpace H'] [NormedAddCommGroup H']
    [NormedSpace ℝ H'] {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] (f : P → ℝ)
    (z : P) : Prop :=
  ∃ (e : OpenPartialHomeomorph P H') (_ : e ∈ atlas H' P) (_ : z ∈ e.source) (v w : H'),
    ∀ (c d : ℝ), (c, d) ≠ 0 →
      (fderiv ℝ (fderiv ℝ (fun x : H' => f (e.symm x))) (e z))
        (c • v + d • w) (c • v + d • w) < 0

/-- The predicate `HasNegDefPlane f z` unfolded in a *specific* chart: it is enough to exhibit the
plane in any one chart of the atlas. -/
theorem hasNegDefPlane_of_chart {H' : Type*} [TopologicalSpace H'] [NormedAddCommGroup H']
    [NormedSpace ℝ H'] {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] {f : P → ℝ} {z : P}
    {e : OpenPartialHomeomorph P H'} (he : e ∈ atlas H' P) (hz : z ∈ e.source) {v w : H'}
    (h : ∀ (c d : ℝ), (c, d) ≠ 0 →
      (fderiv ℝ (fderiv ℝ (fun x : H' => f (e.symm x))) (e z))
        (c • v + d • w) (c • v + d • w) < 0) :
    HasNegDefPlane H' f z :=
  ⟨e, he, hz, v, w, h⟩

/-! ## 2. Criticality of the polygon energy, intrinsically -/

/-- **The polygon energy is critical at `w`.**  Every smooth curve through `w` that moves a single
interior vertex has vanishing derivative of the energy: the first variation of `gonEnergy` at `w`
vanishes in every direction.  (Stated with `HasDerivAt … 0 0` rather than `deriv … 0 = 0`, which
would be satisfied by a non-differentiable energy as well.) -/
def GonCritical (p : M) {N : ℕ} (w : Fin (N - 1) → M) : Prop :=
  ∀ (i : Fin (N - 1)) (γ : ℝ → M), ContMDiff 𝓘(ℝ) I ∞ γ → γ 0 = w i →
    HasDerivAt (fun t : ℝ => gonEnergy (I := I) p (Function.update w i (γ t))) 0 0

/-- **A straight polygon with equal sides.**  `GonStraight hmet p w d` says: all sides have length
`d`, and at each *interior* vertex the geodesic in the direction of the next vertex passes through
the previous one (so the broken geodesic through the vertices is a smooth geodesic in the interior,
traversed with equal side lengths `d`).  Nothing is required at the base vertex `v₀ = v_N = p`,
where the closed geodesic *loop* may have a corner. -/
def GonStraight (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (p : M) {N : ℕ} (w : Fin (N - 1) → M) (d : ℝ) : Prop :=
  (∀ i : Fin N, gonSideLen (I := I) p w i = d) ∧
  (∀ i : Fin (N - 1), ∃ u : TangentSpace I (gonVert p w ((i : ℕ) + 1)),
      ‖u‖ = d ∧
      Submission.GlobalExp.GExp (cov := cov) hmet (gonVert p w ((i : ℕ) + 1)) u
        = gonVert p w ((i : ℕ) + 2) ∧
      Submission.GlobalExp.GExp (cov := cov) hmet (gonVert p w ((i : ℕ) + 1)) (-u)
        = gonVert p w (i : ℕ))

end

end Work.OddBound
