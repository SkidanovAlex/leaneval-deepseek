import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The polygon model of the loop space (for the odd-dimensional Klingenberg minimax)

This module introduces the finite-dimensional model on which the loop-space minimax of
`Work.OddBound.MinimaxExtraction` is run, and fixes the conventions used by every lemma below it.

## The model

A **closed `N`-gon based at `p`** is a tuple `w : Fin (N-1) → M` of *interior* vertices; the full
vertex list is `gonVert p w : ℕ → M`, with

* `gonVert p w 0 = p`,
* `gonVert p w (i+1) = w i`  for `i : Fin (N-1)`,
* `gonVert p w N = p` (and `gonVert p w i = p` for `i ≥ N`).

Its **energy** is `gonEnergy p w = (N/2) · Σ_{i<N} d(v_i, v_{i+1})²`, the energy of the broken
geodesic through the vertices traversed with equal parameter steps.  The factor `N/2` is the
normalisation that makes the model energy equal to the energy of the broken geodesic in the
equal-parameter parametrisation; in particular `gonEnergy p w ≥ L²/2` where `L = Σ_i d(v_i,v_{i+1})`
is the length of the broken geodesic (Cauchy–Schwarz), with equality iff all sides are equal.

The model space `Fin (N-1) → M` is the manifold `M^{N-1}` (the "space of based `N`-gons"), and
`gonEnergy` is smooth on the open set of *small-sided* polygons — those all of whose consecutive
vertices are closer than the injectivity radius — which contains every polygon
of energy `≤ C` once `N` is large (`√(2C/N)` tends to `0`).

## Why this model

The critical points of `gonEnergy` on the small-sided region are exactly the closed geodesics
(`gonEnergy_critical_geodesic`): the first variation of the squared distance function produces the
"straightness" condition at each vertex.  This is what makes the model the right one for the
minimax: the model is finite-dimensional (so the mountain-pass principle applies), and its critical
points are genuine closed geodesics (so the index computation of `IndexBound`/
`strongIndex.not_dirichletIndexLeOne_of_parallelNormalPair` applies to them).

The vertex function `v τ i = γ (L * i / N)` of a closed geodesic `γ` of period `L` gives the polygon
whose broken geodesic *is* `γ (L * ·)` (for `L/N` below the injectivity radius), which is why the
value bound `polygonValueBound` below is stated with those vertices as the `τ = 0` slice.
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

/-- **The vertex list of the closed `N`-gon with interior vertices `w`.**  The vertices `0` and `N`
are the base point `p`; the vertex `i+1` is `w i` for `i : Fin (N-1)`.  Vertices outside `[0,N]` are
`p`. -/
def gonVert (p : M) {N : ℕ} (w : Fin (N - 1) → M) : ℕ → M :=
  fun i => if h : i = 0 ∨ N ≤ i then p else w ⟨i - 1, by omega⟩

@[simp] theorem gonVert_zero (p : M) {N : ℕ} (w : Fin (N - 1) → M) : gonVert p w 0 = p := by
  simp [gonVert]

theorem gonVert_of_le (p : M) {N : ℕ} (w : Fin (N - 1) → M) {i : ℕ} (hi : N ≤ i) :
    gonVert p w i = p := by
  simp [gonVert, Or.inr hi]

theorem gonVert_succ (p : M) {N : ℕ} (w : Fin (N - 1) → M) {i : ℕ} (hi : i < N - 1) :
    gonVert p w (i + 1) = w ⟨i, hi⟩ := by
  have h1 : i + 1 ≠ 0 := by omega
  have h2 : ¬ N ≤ i + 1 := by omega
  simp [gonVert, h1, h2]

/-- **The length of the `i`-th side of the polygon.** -/
def gonSideLen (p : M) {N : ℕ} (w : Fin (N - 1) → M) (i : ℕ) : ℝ :=
  Submission.Distance.riemannianDist (I := I) (gonVert p w i) (gonVert p w (i + 1))

/-- **The total length of the polygon** (the length of the broken geodesic through its vertices). -/
def gonLength (p : M) {N : ℕ} (w : Fin (N - 1) → M) : ℝ :=
  ∑ i : Fin N, gonSideLen (I := I) p w i

/-- **The polygon energy**: `(N/2) · Σ_{i<N} d(v_i,v_{i+1})²`. -/
def gonEnergy (p : M) {N : ℕ} (w : Fin (N - 1) → M) : ℝ :=
  (N : ℝ) / 2 * ∑ i : Fin N, (gonSideLen (I := I) p w i) ^ 2

/-- **The polygon is small-sided**: every side is shorter than `R`. -/
def GonSmall (p : M) {N : ℕ} (R : ℝ) (w : Fin (N - 1) → M) : Prop :=
  ∀ i : Fin N, gonSideLen (I := I) p w i < R

/-- The Cauchy–Schwarz inequality relating the length of the polygon to its energy:
`L² ≤ 2 · E`.  In particular a polygon of energy `< 2π²/K` has length `< 2π/√K`. -/
theorem gonLength_sq_le_two_mul_gonEnergy (p : M) {N : ℕ} (w : Fin (N - 1) → M) :
    (gonLength (I := I) p w) ^ 2 ≤ 2 * gonEnergy (I := I) p w := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [gonLength, gonEnergy]
  · have hcs : (∑ i : Fin N, gonSideLen (I := I) p w i) ^ 2
        ≤ (N : ℝ) * ∑ i : Fin N, (gonSideLen (I := I) p w i) ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
        (f := fun i : Fin N => gonSideLen (I := I) p w i)
    have hNn : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
    rw [gonEnergy, gonLength]
    nlinarith [hcs]

end

end Work.OddBound
