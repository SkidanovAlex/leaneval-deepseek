import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.fold_source_open_dvor
import Submission.Work.FoldInst.foldPsi_hagree

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-- **The chart value on `M̄` is computed by any lift in the generic part.**  If `x` lies in one of
the Voronoi pieces `Dvor i r`, then `foldPhi i (mk x)` — which is `foldPsi i` evaluated at the
chosen representative `Quotient.out (mk x)` of the class of `x` — agrees with `foldPsi i x`, because
the two points are identified (`rel x (Quotient.out (mk x))`) and `foldPsi i` is invariant under the
identification relation `rel` (`foldPsi_hagree`). -/
theorem foldPhi_mk (i : Fin 98) {x : Xbar} (hx : x ∈ ⋃ r : Fin (foldCodim i) → Bool, Dvor i r) :
    foldPhi i (mk x) = foldPsi i x := by
  have h1 : Quotient.mk setoid (Quotient.out (mk x)) = Quotient.mk setoid x :=
    Quotient.out_eq (mk x)
  exact foldPsi_hagree i hx (rel_symm (Quotient.exact h1))

end Work.FoldInst
