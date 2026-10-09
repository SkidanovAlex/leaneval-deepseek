import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

namespace Work.SSGRoute.PT

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Transport of the degree-one bridge along a propositional change of the group hom defining the
action.**  For `φ₁ φ₂ : H →* G` which are propositionally equal, the `Ext¹`-class of a `1`-cocycle
`z₁` for the `φ₁`-action equals the class of `z₂` for the `φ₂`-action, transported along the
`eqToHom` between the two coefficient representations.  The proof is `subst`: after substituting the
equality of the homs (and of the cocycles) the two sides are the *same* class, and the `eqToHom`
becomes the identity. -/
theorem gammaZ1_eqToHom_transport {H G : Type} [Group H] [Group G] (X : Type) [AddCommGroup X]
    [DistribMulAction G X] [SMulCommClass G Coeff X]
    (φ₁ φ₂ : H →* G) (hφ : φ₁ = φ₂)
    (hres : Rep.res φ₂ (modRep G X) = Rep.res φ₁ (modRep G X))
    (z₁ : @Work.GroupCohomology.Z1 H X _ _ (DistribMulAction.compHom X φ₁))
    (z₂ : @Work.GroupCohomology.Z1 H X _ _ (DistribMulAction.compHom X φ₂))
    (hψ : ∀ h, z₁.1 h = z₂.1 h)
    (C₁ : @SMulCommClass H Coeff X (DistribMulAction.compHom X φ₁).toSMul _)
    (C₂ : @SMulCommClass H Coeff X (DistribMulAction.compHom X φ₂).toSMul _) :
    @Work.SSGRoute.ExtH1.gammaZ1 H _ X _ (DistribMulAction.compHom X φ₁) C₁
        (Work.SSGRoute.augSES_shortExact H) z₁
      = (@Work.SSGRoute.ExtH1.gammaZ1 H _ X _ (DistribMulAction.compHom X φ₂) C₂
          (Work.SSGRoute.augSES_shortExact H) z₂).comp
        (Abelian.Ext.mk₀ (eqToHom hres)) (add_zero 1) := by
  subst hφ
  have hz : z₁ = z₂ := Subtype.ext (funext hψ)
  subst hz
  rw [show hres = rfl from Subsingleton.elim _ _]
  simp only [eqToHom_refl]
  rw [Abelian.Ext.comp_mk₀_id]

end Work.SSGRoute.PT
