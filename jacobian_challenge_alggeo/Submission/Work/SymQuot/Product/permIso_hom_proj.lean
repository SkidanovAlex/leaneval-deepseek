import Mathlib
import Submission.Work.SymQuot.Product
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.Product

theorem permIso_hom_proj {K : Type*} [Field K] (X : Work.GCBasics.Sch K) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    CategoryTheory.CategoryStruct.comp (Work.SymQuot.permIso X σ).hom
        (CategoryTheory.Limits.Pi.π (fun _ : Fin n => X) i) =
      CategoryTheory.Limits.Pi.π (fun _ : Fin n => X) (σ.symm i) := by
  simp only [Work.SymQuot.permIso, Work.SymQuot.prod,
    CategoryTheory.Limits.Pi.whiskerEquiv_hom,
    CategoryTheory.Limits.Pi.map'_comp_π]
  simp

end Work.SymQuot.Product
