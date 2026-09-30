import Mathlib
import Submission.Work.ConvexCells.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ConvexCells

open scoped BigOperators

/-- The affine realization of the open simplex of a flag lies in the polytope. -/
theorem FlagPt_mem {d : ℕ} {P : PolytopeData d} (h : P.Ok) (s : P.FlagPt) :
    s.toE' ∈ P.Pset := by
  refine P.Pset_convex.sum_mem (t := Finset.univ)
    (fun i _ => le_of_lt (s.wt_pos i)) s.wt_sum (fun i _ => ?_)
  exact PolytopeData.posR_mem_Pset P h (s.flag.get i)

end Work.ConvexCells
