import Mathlib
import Submission.Work.Surgery.Gluing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The double of a compact manifold with boundary

`Work.ThomBordism.BoundaryMaximalIsotropic` (the crux of `Work.ThomBordism.BoundarySigma`) is the
maximality half of middle-dimensional Poincaré–Lefschetz duality for the pair `(W, ∂W)`.  Its
classical proof doubles `W` along `∂W` and uses the *closed* Poincaré duality of the resulting
`9`-manifold `D = W ∪_∂W W̄` (`Work.Cohomology.pd_good_univ` needs only a `ChartedSpace`,
`CompactSpace` and `T2Space` on `D`, no smoothness).

This file only *defines* the double, using the point-set gluing construction of
`Submission/Work/Surgery/Gluing.lean` with the **identity** homeomorphism of the boundary.  The
identity gluing is what makes the construction elementary: at a boundary point the two halves of the
double are identified by `x ↦ x`, so the seam chart of `D` is built from the *same* chart of `W` on
both copies (`e` on the first half, `refl ∘ e` on the second), and the source of that chart is open
in `D` because its preimages on the two copies of `W` are open in `W`.  In particular **no collar
neighbourhood of `∂W` in `W` is needed**, and no smoothness: the surgery chapter's
`Work.Surgery.SmoothGlue`/`SmoothCollar` inputs (which need `C^∞` and a collar) are *not* used.

## Contents

* `Work.ThomBordism.doubleData` — the gluing data `GlueData n M M` with `φ = id`;
* `Work.ThomBordism.Double` — the glued space `D = M ∪_∂M M`;
* `Work.ThomBordism.doubleQ`, `doubleιM`, `doubleιN` — the quotient map and the two inclusions,
  with their basic API (`doubleQ_inl`, `doubleQ_inr`, injectivity, the seam description).
-/

set_option backward.isDefEq.respectTransparency false

open scoped Manifold Topology
open Function

namespace Work.ThomBordism

noncomputable section

/-- **The gluing data of the double** of a manifold with boundary along the identity of its
boundary. -/
def doubleData (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] : Work.Surgery.GlueData n M M :=
  ⟨Homeomorph.refl ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)⟩

/-- **The double** `D = M ∪_∂M M` of a manifold with boundary: two copies of `M` glued along their
boundaries by the identity. -/
abbrev Double (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] : Type _ :=
  (doubleData n M).Glued

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The quotient map of the double. -/
def doubleQ : M ⊕ M → Double n M := (doubleData n M).q

/-- The inclusion of the first copy of `M` into its double. -/
def doubleιM : M → Double n M := fun x => doubleQ (Sum.inl x)

/-- The inclusion of the second copy of `M` into its double. -/
def doubleιN : M → Double n M := fun y => doubleQ (Sum.inr y)

@[simp] theorem doubleQ_inl (x : M) :
    doubleQ (n := n) (M := M) (Sum.inl x) = doubleιM (n := n) (M := M) x := rfl

@[simp] theorem doubleQ_inr (y : M) :
    doubleQ (n := n) (M := M) (Sum.inr y) = doubleιN (n := n) (M := M) y := rfl

theorem continuous_doubleQ : Continuous (doubleQ (n := n) (M := M)) :=
  (doubleData n M).continuous_q

theorem continuous_doubleιM : Continuous (doubleιM (n := n) (M := M)) :=
  (continuous_doubleQ (n := n) (M := M)).comp continuous_inl

theorem continuous_doubleιN : Continuous (doubleιN (n := n) (M := M)) :=
  (continuous_doubleQ (n := n) (M := M)).comp continuous_inr

theorem doubleιM_injective : Injective (doubleιM (n := n) (M := M)) :=
  (doubleData n M).ιM_injective

theorem doubleιN_injective : Injective (doubleιN (n := n) (M := M)) :=
  (doubleData n M).ιN_injective

/-- **The two copies of `M` meet exactly in the boundary**: `ιM x = ιN y` iff `x = y` is a
boundary point. -/
theorem doubleιM_eq_ιN_iff {x y : M} :
    doubleιM (n := n) (M := M) x = doubleιN (n := n) (M := M) y ↔
      ∃ p : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M, x = p.1 ∧ y = p.1 := by
  have h := (doubleData n M).ιM_eq_ιN_iff (x := x) (y := y)
  have hι : (doubleData n M).ιM x = doubleιM (n := n) (M := M) x := rfl
  have hν : (doubleData n M).ιN y = doubleιN (n := n) (M := M) y := rfl
  rw [← hι, ← hν]
  simpa [doubleData] using h

/-- A point of the interior of `M` is not identified with any point of the second copy. -/
theorem double_interior_disjoint {x : M}
    (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) {y : M} :
    doubleιM (n := n) (M := M) x ≠ doubleιN (n := n) (M := M) y :=
  (doubleData n M).interior_disjoint hx

/-- **The double of a compact manifold is compact** (the quotient of a compact space). -/
theorem doubleCompact [CompactSpace M] : CompactSpace (Double n M) :=
  (doubleData n M).compactSpace

end

end Work.ThomBordism
