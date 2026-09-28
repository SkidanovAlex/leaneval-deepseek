import Mathlib
import Submission.Work.SSS.hornCok_d_faceLift_chain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

theorem ezLinSnd_bdry_elem (P t : ℕ) (X Y : SSet.{0}) (σ : X.obj (Opposite.op (SimplexCategory.mk (P+1))))
    (z : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X t)
    (hz : (ModuleCat.Hom.hom ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d t
      ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom (((CategoryTheory.MonoidalCategoryStruct.tensorObj X Y).chainComplex (ModuleCat.of ℤ ℤ)).d ((P+1)+t) (P+t)))
        ((ModuleCat.Hom.hom (Work.SSS.ezLinSnd (P+1) t X Y σ)) z)
      = ∑ i : Fin (P+2), (-1 : ℤ)^((i:ℕ)) •
          ((ModuleCat.Hom.hom (Work.SSS.ezLinSnd P t X Y (X.δ i σ))) z) := by
  rcases t with _ | q
  · simpa using hcdfl_bd_zero P X Y σ z
  · rw [hcdfl_bd_succ P q X Y σ z]
    have hzq : (ModuleCat.Hom.hom ((Y.chainComplex ezR).d (q+1) q)) z = 0 := by
      have h := hz
      rw [ChainComplex.next_nat_succ] at h
      exact h
    rw [hzq, map_zero, map_zero, zsmul_zero, add_zero]

end Work.SSS
