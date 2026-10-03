import Mathlib
import Submission.Work.ORHomAlg.JL52.BrownDefs

namespace Work.ORHomAlg.JL52

universe u

/-- Jaikin-Zapirain--Linton, Lemma 5.2 (2), functorial form (the isomorphism cited as
Brown, *Cohomology of Groups*, Proposition III.2.2): let `A` be a left and right `K[G]`-module
whose `K`-actions are compatible with both `K[G]`-actions, and whose left `K[G]`-action is the
antipode-twisted right action in the sense of `hA` (i.e. `A` is simultaneously `L` and `L*`).
Then the functor `X ↦ A ⊠[K[G]] X` (from left `K[G]`-modules to abelian groups) is naturally
isomorphic to the functor `X ↦ K ⊠[K[G]] (A ⊗[K] X)`, where `K` carries the trivial right
`K[G]`-module structure (`Work.ORHomAlg.JL52.instTrivRightModule`) and `A ⊗[K] X` the diagonal
`K[G]`-module structure of `DiagTensorDefs`.  The comparison map is `a ⊠ x ↦ 1 ⊠ (a ⊗ x)`; it is
well defined exactly because of `hA`, and its inverse is induced by `a ⊗ x ↦ a ⊠ x`. -/
theorem brownFunctorIso (K : Type u) [Field K] (G : Type u) [Group G]
    (A : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [IsScalarTower K (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ A] [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ A]
    [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ A]
    (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a) :
    Nonempty (CategoryTheory.Iso (Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) A)
      (CategoryTheory.Functor.comp (Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) A)
        (Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) K))) :=
  ⟨Work.ORHomAlg.JL52.brownNatIso (K := K) (G := G) (A := A) hA⟩

end Work.ORHomAlg.JL52
