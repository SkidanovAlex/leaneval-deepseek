import Mathlib

namespace Work.ORLocInd.FKSKernel

theorem kerCompMulEquiv {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (φ : B →* C) :
    Nonempty ((φ.comp (e : A →* B)).ker ≃* φ.ker) := by
  refine ⟨{ toFun := fun x => ⟨e (x : A), by
              have hx : φ (e (x : A)) = 1 := x.2
              simpa using hx⟩
            invFun := fun y => ⟨e.symm (y : B), by
              have hy : φ (y : B) = 1 := y.2
              show φ (e (e.symm (y : B))) = 1
              rw [e.apply_symm_apply]
              exact hy⟩
            left_inv := fun x => by apply Subtype.ext; simp
            right_inv := fun y => by apply Subtype.ext; simp
            map_mul' := fun x y => Subtype.ext (map_mul e (x : A) (y : A)) }⟩

end Work.ORLocInd.FKSKernel
