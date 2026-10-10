import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3

open TensorProduct

set_option linter.style.haveILetI false in
/-- Base change transitivity for the tower `R → S → T`:
`(A ⊗[R] S) ⊗[S] T ≃ A ⊗[R] T`, where `A ⊗[R] S` carries the `S`-algebra structure
given by the right factor (`Algebra.TensorProduct.rightAlgebra`). -/
theorem tensorProduct_tower {R S T A : Type*} [CommRing R] [CommRing S] [CommRing T]
    [CommRing A] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra R A] :
    letI : Algebra S (TensorProduct R A S) := Algebra.TensorProduct.rightAlgebra
    Nonempty ((TensorProduct S (TensorProduct R A S) T) ≃+* (TensorProduct R A T)) := by
  letI : Algebra S (TensorProduct R A S) := Algebra.TensorProduct.rightAlgebra
  refine ⟨?e⟩
  exact ((Algebra.TensorProduct.congr (Algebra.TensorProduct.commRight R S A).symm AlgEquiv.refl).toRingEquiv.trans
    ((Algebra.TensorProduct.comm S (TensorProduct R S A) T).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange R S T T A).toRingEquiv.trans
        (Algebra.TensorProduct.comm R T A).toRingEquiv)))

end Work.K3
