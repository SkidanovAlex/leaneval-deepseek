import Mathlib
import Submission.Work.Projection.TransverseDefs
import Submission.Work.Projection.mfderiv_chartAt_decomp
import Submission.Work.Whitney.LocalModel

/-!
# Double points of a self-map of `ℝ^{2n}` and their signed determinant

For an immersion `f : M → ℝ^{2n}` of a smooth `n`-manifold, this file records the two basic
notions used in Whitney's self-intersection cancellation.

* `Work.Whitney.doubleSet f` — the set of ordered pairs `(p, q)`, `p ≠ q`, with `f p = f q`.
* `Work.Whitney.chartRepM f p` — the chart representation `u ↦ f (chartAt p).symm u` of `f` at `p`
  (a map `ℝⁿ → ℝ^{2n}`, smooth on the chart target).
* `Work.Whitney.doubleDet f p q u v` — the **signed determinant** of the transverse double point:
  the determinant of the "two sheets" map `(x, y) ↦ D(chartRepM f p) u x + D(chartRepM f q) v y`,
  read as an endomorphism of `ℝⁿ × ℝⁿ` through the standard block identification
  `Work.Projection.pairEquiv`.  It is nonzero exactly when `f` is an immersion at `p` and `q` and
  the two tangent images span `ℝ^{2n}` (`doubleDet_ne_zero_iff`); it changes sign by `(-1)^n` when
  the two sheets are swapped (`doubleDet_swap`), which is why for odd `n` the "ordered" count of
  double points vanishes identically.

The *sign* of `doubleDet` is the local intersection number of the two sheets, computed in the
charts at `p` and `q`; comparing the signs of two double points (all of whose preimages lie in the
same two charts) is what decides whether a pair of double points can be cancelled by the Whitney
trick.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- The set of *ordered* double points of a map `f`: pairs `(p, q)` with `p ≠ q` and `f p = f q`. -/
def doubleSet {M Y : Type*} (f : M → Y) : Set (M × M) := {p | p.1 ≠ p.2 ∧ f p.1 = f p.2}

@[simp] theorem mem_doubleSet {M Y : Type*} {f : M → Y} {p : M × M} :
    p ∈ doubleSet f ↔ p.1 ≠ p.2 ∧ f p.1 = f p.2 := Iff.rfl

/-- The chart representation of `f : M → ℝ^{2n}` at `p`, as a map on `ℝⁿ`. -/
noncomputable def chartRepM {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p : M) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun u => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u)

/-- **The signed determinant of a (candidate) double point.**  For `f : M → ℝ^{2n}`, points
`p, q` and chart parameters `u` (at `p`) and `v` (at `q`), this is the determinant of the "two
sheets" map `(x, y) ↦ D (chartRepM f p) u x + D (chartRepM f q) v y` composed with the standard
block identification `pairEquiv n`; it vanishes exactly when the two sheets fail to be transverse
there. -/
noncomputable def doubleDet {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p q : M)
    (u v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  LinearMap.det (((Work.Projection.pairEquiv n).toLinearMap).comp
    (((fderiv ℝ (chartRepM f p) u).coprod (fderiv ℝ (chartRepM f q) v)).toLinearMap))

end Work.Whitney
