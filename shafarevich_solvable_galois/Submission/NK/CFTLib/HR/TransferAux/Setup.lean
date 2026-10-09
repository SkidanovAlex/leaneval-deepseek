import Mathlib
import Submission.NK.CFTLib.HR.TransferAux.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.CFTLib.HR.TransferAux

open CategoryTheory

/-- The kernel of the restriction `Gal(E/K) →* Gal(M/K)`, i.e. the Galois group of `E` over the
image of `M` in `E`. -/
noncomputable abbrev rN (K M E : Type) [Field K] [Field M] [Field E] [Algebra K M]
    [Algebra K E] [Algebra M E] [IsScalarTower K M E] [Normal K M] : Subgroup (E ≃ₐ[K] E) :=
  (AlgEquiv.restrictNormalHom (K₁ := E) (E := M)).ker

section

variable {K M E : Type} [Field K] [Field M] [Field E] [Algebra K M]
    [Algebra K E] [Algebra M E] [IsScalarTower K M E] [Normal K M] [Normal K E]

/-- **The quotient isomorphism** `Gal(E/K) ⧸ Gal(E/M) ≃* Gal(M/K)`. -/
noncomputable def rQuot (K M E : Type) [Field K] [Field M] [Field E] [Algebra K M]
    [Algebra K E] [Algebra M E] [IsScalarTower K M E] [Normal K M] [Normal K E] :
    (E ≃ₐ[K] E) ⧸ rN K M E ≃* (M ≃ₐ[K] M) :=
  QuotientGroup.liftEquiv (rN K M E)
    (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := E)) rfl

lemma rQuot_apply (σ : E ≃ₐ[K] E) :
    rQuot K M E (QuotientGroup.mk' (rN K M E) σ)
      = AlgEquiv.restrictNormalHom (K₁ := E) (E := M) σ := by
  rw [show rQuot K M E (QuotientGroup.mk' (rN K M E) σ)
      = QuotientGroup.lift (rN K M E) (AlgEquiv.restrictNormalHom (K₁ := E) (E := M))
          (le_of_eq rfl) (QuotientGroup.mk' (rN K M E) σ) from rfl]
  exact QuotientGroup.lift_mk' (N := rN K M E) (le_of_eq rfl) σ

lemma rQuot_comp_mk' :
    (rQuot K M E).toMonoidHom.comp (QuotientGroup.mk' (rN K M E))
      = AlgEquiv.restrictNormalHom (K₁ := E) (E := M) := by
  rw [show (rQuot K M E).toMonoidHom
      = QuotientGroup.lift (rN K M E) (AlgEquiv.restrictNormalHom (K₁ := E) (E := M))
          (le_of_eq rfl) from rfl]
  exact QuotientGroup.lift_comp_mk' (rN K M E)
    (AlgEquiv.restrictNormalHom (K₁ := E) (E := M)) (le_of_eq rfl)

lemma rQuot_symm_comp :
    (rQuot K M E).symm.toMonoidHom.comp (AlgEquiv.restrictNormalHom (K₁ := E) (E := M))
      = QuotientGroup.mk' (rN K M E) := by
  ext σ
  show (rQuot K M E).symm (AlgEquiv.restrictNormalHom (K₁ := E) (E := M) σ)
    = QuotientGroup.mk' (rN K M E) σ
  exact (MulEquiv.symm_apply_eq (rQuot K M E)).mpr (by
    rw [show rQuot K M E (QuotientGroup.mk' (rN K M E) σ)
        = QuotientGroup.lift (rN K M E) (AlgEquiv.restrictNormalHom (K₁ := E) (E := M))
            (le_of_eq rfl) (QuotientGroup.mk' (rN K M E) σ) from rfl]
    exact QuotientGroup.lift_mk' (N := rN K M E) (le_of_eq rfl) σ)

end

end NK.CFTLib.HR.TransferAux
