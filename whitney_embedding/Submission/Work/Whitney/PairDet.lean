import Mathlib
import Submission.Work.Whitney.DoubleDetC

/-!
# Comparing the signs of two double points that live in two different charts

The Whitney cancellation needs the *relative sign* of two double points `P` and `Q` of a smooth
immersion `f : M → ℝ^{2n}`.  The sign of a single double point is only defined relative to a
trivialisation of the tangent bundle at its two preimages; when the two double points are paired by
arcs `p₁ → q₁` and `p₂ → q₂` that lie inside two charts `c₁` and `c₂`, the charts themselves give
the trivialisations along the two arcs, and the relative sign is then computed by the single number

`pairDet f c₁ c₂ p q = det (pairEquiv n ∘ (D (f ∘ c₁.symm) (c₁ p) ⊕ D (f ∘ c₂.symm) (c₂ q)))`.

Evaluated at the first preimages of the two double points and at the second preimages, this gives
the two signs whose product is the sign of the bigon:

`pairDet f c₁ c₂ p₁ p₂ * pairDet f c₁ c₂ q₁ q₂`.

When `c₁ = c₂ = c` this is exactly `Work.Whitney.doubleDetC f c` (`pairDet_self`), and when
`c₁ = chartAt p`, `c₂ = chartAt q` it is exactly the intrinsic `Work.Whitney.doubleDet` at the
chart coordinates of the two points (`pairDet_chartAt`).
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **The two-chart signed determinant of a (candidate) double point.**  For `f : M → ℝ^{2n}` and
two charts `c₁`, `c₂`, the number
`det (pairEquiv n ∘ ((D (f ∘ c₁.symm) (c₁ a)) coprod (D (f ∘ c₂.symm) (c₂ b))))`. -/
noncomputable def pairDet {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (a b : M) : ℝ :=
  LinearMap.det (((Work.Projection.pairEquiv n).toLinearMap).comp
    (((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₁.symm u)) (c₁ a)).coprod
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u)) (c₂ b))).toLinearMap))

/-- With one chart, `pairDet` is the single-chart signed determinant `doubleDetC`. -/
theorem pairDet_self {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (a b : M) :
    pairDet f c c a b = doubleDetC f c a b := rfl

/-- With the charts at the two points, `pairDet` is the intrinsic `doubleDet` evaluated at the
chart coordinates of the two points. -/
theorem pairDet_chartAt {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p q : M) :
    pairDet f (chartAt (EuclideanSpace ℝ (Fin n)) p)
        (chartAt (EuclideanSpace ℝ (Fin n)) q) p q
      = doubleDet f p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)
          ((chartAt (EuclideanSpace ℝ (Fin n)) q) q) := rfl

end Work.Whitney
