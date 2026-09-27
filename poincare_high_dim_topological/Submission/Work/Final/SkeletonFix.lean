import Submission.Work.Cells.Connell.Defs
import Submission.Work.Geo.DualStretch.dual_stretch

/-!
# `Work.Final.SkeletonDataFin`: the repaired `SkeletonData` interface

`Work.Cells.Connell.SkeletonData` (area `A6`/`G7`) and the `SkeletonData`-shaped fields packaged
there cannot be instantiated with the skeleta of `Work.Geo.DualStretch`: its `low_closed` and
`high_closed` fields are quantified over **all** geometric simplicial complexes, and the `p`-skeleton
of an *infinite* complex need not be closed (see `Submission/Work/Final/Defs.lean` for the
counterexample; `Work.Final.not_forall_isClosed_Low` formalises it).  `Work.Final.skelLow` /
`skelHigh` are the workaround used by the final assembly.

This file records the *proper* repair: the same structure with `P.faces.Finite` added to the four
fields that need it (`low_closed`, `high_closed`, `low_dom`, `high_dom` — each of them is *false*
for the `p`-skeleton of a general infinite complex, and each of them is only ever used on the finite
triangulation produced by `CubeTriangulationForm`).  With that hypothesis the structure is inhabited
by the **genuine** skeleta `Work.Geo.DualStretch.Low` / `High`; see
`Work.Final.skeletonDataFin`.

The fields `low_sub`, `high_sub` and `dual_stretch` need no change: they are already quantified
correctly (`dual_stretch` carries `P.faces.Finite`, and being contained in `P.space` is true for the
union over all faces).

If the owning areas adopt this repair, `Work.Final.skeletonData` becomes the special case supplied
by the finite-index definitions and the `SkeletonDataFin` of this file can replace it verbatim.
-/

open Set Metric

namespace Work.Final

/-- The `Work.Geo.DualStretch` skeleta with the closure fields restricted to finite complexes. -/
structure SkeletonDataFin (n : ℕ) where
  /-- the low (`p`-skeleton) part -/
  Low : PL.Cx n → ℕ → Set (PL.E n)
  /-- the high (dual skeleton) part -/
  High : PL.Cx n → ℕ → Set (PL.E n)
  /-- `Low` lies in the polyhedron -/
  low_sub : ∀ (P : PL.Cx n) (p : ℕ), Low P p ⊆ P.space
  /-- `High` lies in the polyhedron -/
  high_sub : ∀ (P : PL.Cx n) (p : ℕ), High P p ⊆ P.space
  /-- `Low` is closed for a finite complex -/
  low_closed : ∀ (P : PL.Cx n) (p : ℕ), P.faces.Finite → IsClosed (Low P p)
  /-- `High` is closed for a finite complex -/
  high_closed : ∀ (P : PL.Cx n) (p : ℕ), P.faces.Finite → IsClosed (High P p)
  /-- the `p`-skeleton of a finite complex is `p`-dimensional -/
  low_dom : ∀ (P : PL.Cx n) (p : ℕ), P.faces.Finite → PL.DomDim (Low P p) p
  /-- the dual `(n-p-1)`-skeleton of a finite complex is `(n-p-1)`-dimensional -/
  high_dom : ∀ (P : PL.Cx n) (p : ℕ), P.faces.Finite →
    PL.DomDim (High P p) ((n - p - 1 : ℕ) : ℤ)
  /-- `dual_stretch` (`G7`) -/
  dual_stretch : ∀ (p : ℕ) (β α : ℝ), p < n → 0 < α → α < β → (P : PL.Cx n) →
    P.faces.Finite → P.space = PL.closedCube β → ∀ (N₁ N₂ : Set (PL.E n)),
    IsOpen N₁ → IsOpen N₂ → Low P p ⊆ N₁ → High P p ⊆ N₂ →
    ∃ h : PL.E n ≃ₜ PL.E n, (∀ x, x ∉ PL.openCube β → h x = x) ∧
      (∀ s ∈ P.faces, h '' PL.simp s = PL.simp s) ∧
      PL.closedCube α ⊆ h '' N₁ ∪ N₂

end Work.Final
