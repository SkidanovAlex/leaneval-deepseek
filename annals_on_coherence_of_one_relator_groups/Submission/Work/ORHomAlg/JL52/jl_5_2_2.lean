/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Jaikin-Zapirain--Linton, Lemma 5.2 (2)

For a field `K`, a group `G`, left `K[G]`-modules `M`, `N` and a right `K[G]`-module `L`, and every
`k : ℕ`,

  `Tor_k^{K[G]}(L, M ⊗_K N) ≅ Tor_k^{K[G]}(N*, M ⊗_K L*)`,

where `M ⊗_K N` and `M ⊗_K L*` carry the diagonal `K[G]`-action
(`Work.ORHomAlg.JL52.instDiagModule`) and where `N*` (a right `K[G]`-module) and `L*` (a left
`K[G]`-module) are the duals with respect to the antipode `Work.ORHomAlg.antipodeEquiv`, realised
as the type synonym `Work.ORHomAlg.DualMod`.

The proof is the paper's: the "Brown" natural isomorphism
`Work.ORHomAlg.JL52.brownFunctorIso` gives `L ⊠[K[G]] X ≅ K ⊠[K[G]] (L* ⊗_K X)` for every left
`K[G]`-module `X`; applying it with `X = M ⊗_K N` and with (`X = M ⊗_K L*`, `L` replaced by `N*`,
using `(N*)* = N`), and comparing the two middle modules by the flip
`Work.ORHomAlg.JL52.middleIsoCat`, gives the result.

## Main result

* `Work.ORHomAlg.JL52.jl_5_2_2`.
-/
import Mathlib
import Submission.Work.ORHomAlg.Dual
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs
import Submission.Work.ORHomAlg.JL52.diagTensor_preservesHomology
import Submission.Work.ORHomAlg.JL52.smulCommClassDiag
import Submission.Work.ORHomAlg.JL52.brownFunctorIso
import Submission.Work.ORHomAlg.JL52.diagTensor_regular_projective
import Submission.Work.ORHomAlg.JL52.diagTensor_preservesProjectiveObjects
import Submission.Work.ORHomAlg.JL52.middleIso
import Submission.Work.ORHomAlg.JL52.middleIsoCat
import Submission.Work.ORHomAlg.leftDerived_comp_of_preservesProjectiveObjects

namespace Work.ORHomAlg.JL52

open CategoryTheory
open scoped TensorProduct

universe u

set_option maxHeartbeats 800000

theorem jl_5_2_2 (K G : Type u) [Field K] [Group G]
    (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
    [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ L] [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ L]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [SMulCommClass K (MonoidAlgebra K G) M]
    (N : Type u) [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
    [IsScalarTower K (MonoidAlgebra K G) N] [SMulCommClass K (MonoidAlgebra K G) N]
    (k : ℕ) :
    Nonempty (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) k L (TensorProduct K M N) ≃ₗ[ℤ]
      Work.ORHomAlg.Tor (R := MonoidAlgebra K G) k (Work.ORHomAlg.DualMod N)
        (TensorProduct K M (Work.ORHomAlg.DualMod L))) := by
  -- instances for the two duals
  haveI : SMulCommClass K (MonoidAlgebra K G) (Work.ORHomAlg.DualMod L) :=
    Work.ORHomAlg.DualMod.instSMulCommClassOfRight K G L
  haveI : SMulCommClass K (MonoidAlgebra K G) (Work.ORHomAlg.DualMod N) :=
    Work.ORHomAlg.DualMod.instSMulCommClassOfLeft K G N
  haveI : IsScalarTower K (MonoidAlgebra K G) (Work.ORHomAlg.DualMod L) :=
    Work.ORHomAlg.DualMod.instIsScalarTowerOfRight K G L
  haveI : IsScalarTower K (MonoidAlgebra K G) (Work.ORHomAlg.DualMod N) :=
    Work.ORHomAlg.DualMod.instIsScalarTowerOfLeft K G N
  haveI : SMulCommClass K (MonoidAlgebra K G) (TensorProduct K M N) := smulCommClassDiag K G M N
  haveI : SMulCommClass K (MonoidAlgebra K G) (TensorProduct K M (Work.ORHomAlg.DualMod L)) :=
    smulCommClassDiag K G M (Work.ORHomAlg.DualMod L)
  haveI : SMulCommClass K (MonoidAlgebra K G) (TensorProduct K M (Work.ORHomAlg.DualMod N)) :=
    smulCommClassDiag K G M (Work.ORHomAlg.DualMod N)
  -- the two Brown isomorphisms and the middle isomorphism
  obtain ⟨eL⟩ := brownFunctorIso K G (Work.ORHomAlg.DualMod L)
    (fun g a => Work.ORHomAlg.DualMod.single_smul_eq_op_inv_smul_of_right K G L g a)
  obtain ⟨eN⟩ := brownFunctorIso K G (Work.ORHomAlg.DualMod N)
    (fun g a => Work.ORHomAlg.DualMod.single_smul_eq_op_inv_smul_of_left K G N g a)
  -- the functors
  let PhiL := Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) (Work.ORHomAlg.DualMod L)
  let PhiN := Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) (Work.ORHomAlg.DualMod N)
  let PhiK := Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) K
  let DL := diagTensor (K := K) (G := G) (Work.ORHomAlg.DualMod L)
  let DN := diagTensor (K := K) (G := G) (Work.ORHomAlg.DualMod N)
  haveI : DL.Additive := diagTensor_additive (Work.ORHomAlg.DualMod L)
  haveI : DN.Additive := diagTensor_additive (Work.ORHomAlg.DualMod N)
  haveI : DL.PreservesHomology := diagTensor_preservesHomology K G (Work.ORHomAlg.DualMod L)
  haveI : DN.PreservesHomology := diagTensor_preservesHomology K G (Work.ORHomAlg.DualMod N)
  haveI : DL.PreservesProjectiveObjects :=
    diagTensor_preservesProjectiveObjects K G (Work.ORHomAlg.DualMod L)
  haveI : DN.PreservesProjectiveObjects :=
    diagTensor_preservesProjectiveObjects K G (Work.ORHomAlg.DualMod N)
  let X : ModuleCat.{u} (MonoidAlgebra K G) :=
    ModuleCat.of (MonoidAlgebra K G) (TensorProduct K M (Work.ORHomAlg.DualMod N))
  let Y : ModuleCat.{u} (MonoidAlgebra K G) :=
    ModuleCat.of (MonoidAlgebra K G) (TensorProduct K M (Work.ORHomAlg.DualMod L))
  -- isomorphisms of left derived functors
  let bL : PhiL.leftDerived k ≅ (DL ⋙ PhiK).leftDerived k :=
    { hom := NatTrans.leftDerived eL.hom k
      inv := NatTrans.leftDerived eL.inv k
      hom_inv_id := by
        rw [← NatTrans.leftDerived_comp, Iso.hom_inv_id eL, NatTrans.leftDerived_id]
      inv_hom_id := by
        rw [← NatTrans.leftDerived_comp, Iso.inv_hom_id eL, NatTrans.leftDerived_id] }
  let bN : PhiN.leftDerived k ≅ (DN ⋙ PhiK).leftDerived k :=
    { hom := NatTrans.leftDerived eN.hom k
      inv := NatTrans.leftDerived eN.inv k
      hom_inv_id := by
        rw [← NatTrans.leftDerived_comp, Iso.hom_inv_id eN, NatTrans.leftDerived_id]
      inv_hom_id := by
        rw [← NatTrans.leftDerived_comp, Iso.inv_hom_id eN, NatTrans.leftDerived_id] }
  -- comparison of the composite functors with the composite of the derived functors
  obtain ⟨cL⟩ := Work.ORHomAlg.leftDerived_comp_of_preservesProjectiveObjects DL PhiK X k
  obtain ⟨cN⟩ := Work.ORHomAlg.leftDerived_comp_of_preservesProjectiveObjects DN PhiK Y k
  -- the middle isomorphism of `ModuleCat (K[G])`-objects
  let midIso : DL.obj X ≅ DN.obj Y :=
    Classical.choice (middleIsoCat K G (Work.ORHomAlg.DualMod L) M (Work.ORHomAlg.DualMod N))
  -- assemble
  refine ⟨CategoryTheory.Iso.toLinearEquiv ?_⟩
  exact (bL.app X) ≪≫ cL ≪≫ ((PhiK.leftDerived k).mapIso midIso) ≪≫ cN.symm ≪≫ (bN.app Y).symm

end Work.ORHomAlg.JL52
