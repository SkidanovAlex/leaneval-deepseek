import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

theorem extHRestrict_comp_mk0 {G : Type} [Group G] (D : Subgroup G) {A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff D} {n : ℕ} (x : extH A n) (φ : Rep.res D.subtype A ⟶ B) :
    (extHRestrict D x).comp (Abelian.Ext.mk₀ φ) (add_zero n) = extHMap D.subtype φ x := by
  -- Unfold both sides: the left is `(mk₀ u ∘ (x|_D ∘ mk₀ 𝟙)) ∘ mk₀ φ`, the right is
  -- `mk₀ u ∘ (x|_D ∘ mk₀ φ)`, where `u = unitRes D.subtype`.
  simp only [extHRestrict, extHMap, extRes]
  -- Move the postcomposition `mk₀ φ` past the outer Yoneda product `mk₀ u`.
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  -- Move it past the inner Yoneda product, absorbing the identity `mk₀ 𝟙`.
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  simp

end Work.SSGRoute
