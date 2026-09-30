import Mathlib
import Submission.Work.SSSR.hornCok_d_faceLift_chain
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
theorem ezLinSnd_bdry_elem (P t : ℕ) (X Y : SSet.{0}) (σ : X.obj (Opposite.op (SimplexCategory.mk (P+1))))
    (z : (Y.chainComplex (ModuleCat.of R R)).X t)
    (hz : (ModuleCat.Hom.hom ((Y.chainComplex (ModuleCat.of R R)).d t
      ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom (((CategoryTheory.MonoidalCategoryStruct.tensorObj X Y).chainComplex (ModuleCat.of R R)).d ((P+1)+t) (P+t)))
        ((ModuleCat.Hom.hom (Work.SSSR.ezLinSnd (P+1) t X Y σ)) z)
      = ∑ i : Fin (P+2), (-1 : ℤ)^((i:ℕ)) •
          ((ModuleCat.Hom.hom (Work.SSSR.ezLinSnd P t X Y (X.δ i σ))) z) := by
  rcases t with _ | q
  · simpa using hcdfl_bd_zero P X Y σ z
  · rw [hcdfl_bd_succ P q X Y σ z]
    have hzq : (ModuleCat.Hom.hom ((Y.chainComplex (ezR R)).d (q+1) q)) z = 0 := by
      have h := hz
      rw [ChainComplex.next_nat_succ] at h
      exact h
    rw [hzq, map_zero, map_zero, zsmul_zero, add_zero]

end Work.SSSR
