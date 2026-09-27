import Mathlib
import Submission.Work.Projection.Basic

/-!
# The chartwise "bad direction" sets for the Whitney projection argument

For a smooth map `f : M → ℝ^{k+1}` we parametrise the directions of projections
`ℝ^{k+1} → ℝ^k` by vectors `u : ℝ^k`: the projection `projVec u` has kernel spanned by
`(u,1) = vVec u`.  A direction is *bad* if the projection spoils the injectivity or the
immersion property.

Here we define the bad sets in terms of the chart representations of `f`, which makes the
Hausdorff dimension of these sets accessible.
-/

open scoped Manifold ContDiff
open Topology

namespace Work.Projection

variable {n k : ℕ}

/-- The representation `y ↦ f (chart⁻¹ y)` of `f` in the chart at `p`. -/
noncomputable def chartRep {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : M) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (k+1)) :=
  fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)

lemma chartRep_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : M) (x : M)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    chartRep f p ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) = f x := by
  simp only [chartRep, OpenPartialHomeomorph.left_inv _ hx]

/-- `extract` is a section of `u ↦ vVec u`. -/
@[simp] lemma extract_vVec {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) : extract (vVec u) = u := by
  ext i
  simp [extract_apply]

/-- If `z = c • vVec u` with `c ≠ 0`, then `extract z = u`. -/
lemma extract_of_eq_smul_vVec {k : ℕ} (u : EuclideanSpace ℝ (Fin k))
    {z : EuclideanSpace ℝ (Fin (k+1))} {c : ℝ} (hc : c ≠ 0) (hz : z = c • vVec u) :
    extract z = u := by
  subst hz
  exact extract_smul_vVec u hc

/-- The immersion-bad directions, defined chartwise: `u` is bad for the chart at `p` if
`(u,1)` lies in the image of the derivative of the chart representation of `f` at some point
of the chart's target. -/
noncomputable def badImmCharts {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : ℕ → M) : Set (EuclideanSpace ℝ (Fin k)) :=
  {u | ∃ i, ∃ y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).target,
        ∃ w : EuclideanSpace ℝ (Fin n), fderiv ℝ (chartRep f (p i)) y w = vVec u}

/-- The injectivity-bad directions, defined chartwise: `u` is bad if two points in the charts
at `p i` and `p j` have images whose difference is a nonzero multiple of `(u,1)`. -/
noncomputable def badInjCharts {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : ℕ → M) : Set (EuclideanSpace ℝ (Fin k)) :=
  {u | ∃ i j, ∃ y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).target,
        ∃ z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (p j)).target,
        (chartRep f (p i) y - chartRep f (p j) z) (Fin.last k) ≠ 0 ∧
        extract (chartRep f (p i) y - chartRep f (p j) z) = u}

/-- The parametrisation of the immersion-bad set of a single chart. -/
noncomputable def immParam {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : M) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k) :=
  fun yw => extract (fderiv ℝ (chartRep f p) yw.1 yw.2)

/-- The parametrisation of the injectivity-bad set of a pair of charts. -/
noncomputable def injParam {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p q : M) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k) :=
  fun yz => extract (chartRep f p yz.1 - chartRep f q yz.2)

/-- The open set on which the parametrisation of the immersion-bad set of the chart at `p`
is smooth. -/
noncomputable def immDom {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : M) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {yw | yw.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
        (fderiv ℝ (chartRep f p) yw.1 yw.2) (Fin.last k) ≠ 0}

/-- The open set on which the parametrisation of the injectivity-bad set of the charts at
`p`, `q` is smooth. -/
noncomputable def injDom {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p q : M) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {yz | yz.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
        yz.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target ∧
        (chartRep f p yz.1 - chartRep f q yz.2) (Fin.last k) ≠ 0}

end Work.Projection
