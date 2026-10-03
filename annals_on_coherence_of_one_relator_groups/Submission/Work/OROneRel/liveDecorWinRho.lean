import Mathlib
import Submission.Work.OROneRel.liveDecorDefs
import Submission.Work.OROneRel.winRho_winRoot

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The live word of a walk is the `filterMap` of `winRootStep`: the step functions agree
definitionally, because `isLive` *is* the pair of conditions used by `winRootStep`. -/
theorem liveDecor_eq_filterMap_winRootStep (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (J : List ((α × ℤ) × Bool)) :
    liveDecor Wt c lo hi J = J.filterMap (winRootStep Wt c lo hi) := rfl

/-- **The live word of a walk computes the gauge.**  If every edge traversed by `J` lies in the
window, then `winRho` of the live word of `J` is `gaugeMap` of `J`: the letters deleted by
`liveDecor` are exactly the traversals of trivial loop class, and they contribute `1` to the gauge
product, so deleting them leaves `gaugeMap Wt c (mk J)` unchanged.

Both sides are expanded into products over the letters of `J`: `map_prod_eq_of_mk` writes `φ (mk L)`
as the product of the images of the letters of `L`, `winRootList_prod_eq` (which holds for an
arbitrary walk whose edges lie in the window) identifies the product over the deleted word with the
product of the loop classes `coverClass Wt c p`, and `gaugeMap_mk_eq_prod` says the latter is exactly
`gaugeMap Wt c (mk J)`. -/
theorem liveDecorWinRho {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (J : List ((α × ℤ) × Bool))
    (hJ : ∀ p ∈ J, Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) :
    Work.OROneRel.winRho Wt c lo hi
        (FreeGroup.mk (Work.OROneRel.liveDecor Wt c lo hi J)) =
      Work.OROneRel.gaugeMap Wt c (FreeGroup.mk J) := by
  classical
  rw [liveDecor_eq_filterMap_winRootStep Wt c lo hi J,
    ← map_prod_eq_of_mk (winRho Wt c lo hi) (J.filterMap (winRootStep Wt c lo hi)),
    winRootList_prod_eq Wt c lo hi J hJ,
    ← map_prod_eq_of_mk (gaugeMap Wt c) J]
  rfl

end Work.OROneRel
