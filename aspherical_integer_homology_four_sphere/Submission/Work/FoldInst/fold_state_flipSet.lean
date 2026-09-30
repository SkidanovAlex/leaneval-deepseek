import Mathlib
import Submission.Work.FoldInst.CertFlip
import Submission.Work.FoldInst.Voronoi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

theorem fold_state_flipSet (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) :
    ((toG (foldKr i (flipSet r Δ)), foldCr i (flipSet r Δ)) : Gg) =
      wallSum i Δ + ((toG (foldKr i r), foldCr i r) : Gg) := by
  induction Δ using Finset.induction_on generalizing r with
  | empty => simp
  | insert t Δ ht ih =>
    rw [flipSet_insert r Δ ht, wallSum_insert i t Δ ht]
    rw [ih (flipSet r {t})]
    rw [fold_state_flip i t r]
    abel

end Work.FoldInst
