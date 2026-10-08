import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIField.Main

/-- Conjugation gives a monoid homomorphism `A →* MulAut R` whenever `A` normalizes `R`.
This is `Subgroup.normalizerMonoidHom` precomposed with the inclusion `A ↪ N_G(R)`. -/
theorem exists_conjAut_R {G : Type} [Group G] (A R : Subgroup G)
    (hAr : A ≤ Subgroup.normalizer (R : Set G)) :
    ∃ c : ↥A →* MulAut ↥R, ∀ (a : ↥A) (x : ↥R),
      (c a x : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
  refine ⟨R.normalizerMonoidHom.comp (Subgroup.inclusion hAr), fun a x => ?_⟩
  show (((Subgroup.inclusion hAr a : ↥(Subgroup.normalizer (R : Set G))) • x : ↥R) : G)
    = (a : G) * (x : G) * (a : G)⁻¹
  have h : (((Subgroup.inclusion hAr a : ↥(Subgroup.normalizer (R : Set G))) • x : ↥R) : G)
      = ((Subgroup.inclusion hAr a : G)) * (x : G)
          * ((Subgroup.inclusion hAr a : G))⁻¹ := rfl
  rw [h, Subgroup.coe_inclusion]

end Work.AppXIField.Main
