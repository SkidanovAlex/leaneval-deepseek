import Mathlib
import Submission.Work.ORHomAlg.Dual

namespace Work.ORBridgeTor

open TensorProduct MulOpposite

universe u

/-!
## A general fact: two module structures with the same scalar action give a linear equivalence

The two `Module R M` structures occurring below are different *terms* even though their `smul`
functions agree pointwise, so `LinearEquiv.refl` does not apply (the instances are part of the type
of `LinearEquiv`).  The following lemma packages the trivial argument: the identity is linear.
-/

/-- If two `Module R M` structures `P` and `Q` have the same scalar action, then the identity is an
`R`-linear equivalence between `M` with structure `P` and `M` with structure `Q`. -/
theorem linearEquivOfSmulEq (R : Type u) [Semiring R] (M : Type u) [AddCommGroup M]
    (P Q : Module R M)
    (h : ∀ (r : R) (m : M),
      @SMul.smul R M P.toDistribMulAction.toDistribSMul.toSMulZeroClass.toSMul r m =
      @SMul.smul R M Q.toDistribMulAction.toDistribSMul.toSMulZeroClass.toSMul r m) :
    Nonempty (@LinearEquiv R R _ _ (RingHom.id R) _ _ _ M M _ _ P Q) := by
  refine ⟨@LinearEquiv.mk R R _ _ (RingHom.id R) _ _ _ M M _ _ P Q
    (@LinearMap.mk R R _ _ (RingHom.id R) M M _ _ P Q
      { toFun := fun x => x, map_add' := fun a b => rfl }
      (fun r m => h r m))
    (fun x => x) (fun x => rfl) (fun x => rfl)⟩

/-!
`DualMod (DualMod C)` carries `Work.ORHomAlg.DualMod.instModuleOfRight` applied to the right
structure `Work.ORHomAlg.DualMod.instModuleOppositeOfLeft` on `DualMod C`; its action on `C` is
`x • m = (antipodeEquiv K G).symm (antipodeEquiv K G x) • m = x • m`, i.e. it agrees pointwise with
the original left action.  So the identity map is the required isomorphism; use
`Work.ORHomAlg.DualMod.instModuleOfRight_smul` and
`Work.ORHomAlg.DualMod.instModuleOppositeOfLeft_smul`.  (This is not `LinearEquiv.refl`: the two
module instances are different terms even though they agree pointwise.)
-/
theorem dualDualEquiv (K : Type u) [Field K] (G : Type u) [Group G]
    (C : Type u) [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C] :
    Nonempty (Work.ORHomAlg.DualMod (Work.ORHomAlg.DualMod C) ≃ₗ[MonoidAlgebra K G] C) := by
  refine linearEquivOfSmulEq (MonoidAlgebra K G) C
    (Work.ORHomAlg.DualMod.instModuleOfRight K G (Work.ORHomAlg.DualMod C) :
      Module (MonoidAlgebra K G) C)
    (inferInstance : Module (MonoidAlgebra K G) C) ?_
  intro r m
  -- The action of `Work.ORHomAlg.DualMod.instModuleOfRight` on `DualMod C` is
  -- `r • m = antipode r • m` (with the `instModuleOppositeOfLeft` structure), and the latter is
  -- definitionally `antipode⁻¹ (antipode r) • m` (with the given structure on `C`).
  have h1 : @SMul.smul (MonoidAlgebra K G) C
      ((Work.ORHomAlg.DualMod.instModuleOfRight K G (Work.ORHomAlg.DualMod C) :
        Module (MonoidAlgebra K G) C)).toDistribMulAction.toDistribSMul.toSMulZeroClass.toSMul r m
      = @SMul.smul (MonoidAlgebra K G) C
        (inferInstance : Module (MonoidAlgebra K G) C).toDistribMulAction.toDistribSMul.toSMulZeroClass.toSMul
        ((Work.ORHomAlg.antipodeEquiv K G).symm ((Work.ORHomAlg.antipodeEquiv K G) r)) m := rfl
  rw [h1, RingEquiv.symm_apply_apply]

end Work.ORBridgeTor
