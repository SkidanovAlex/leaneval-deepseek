import Mathlib

universe u

namespace Work.DSEQ0

theorem isBaseChange_id_localizationAway
    {A : Type u} [CommRing A] (g : A) {N : Type u} [AddCommMonoid N] [Module A N]
    [Module (Localization.Away g) N] [IsScalarTower A (Localization.Away g) N] :
    IsBaseChange (Localization.Away g) (LinearMap.id : N →ₗ[A] N) :=
  (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) (Localization.Away g)
    (LinearMap.id : N →ₗ[A] N)).mp
    (isLocalizedModule_id (S := Submonoid.powers g) (M := N) (R' := Localization.Away g))

end Work.DSEQ0
