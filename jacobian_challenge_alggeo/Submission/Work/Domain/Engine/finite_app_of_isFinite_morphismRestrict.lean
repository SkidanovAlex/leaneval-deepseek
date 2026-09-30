import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Domain.Engine

open CategoryTheory AlgebraicGeometry

/-- If the restriction `f ∣_ U` of a morphism of schemes `f : G ⟶ X` to an affine open
`U ⊆ X` is finite, then the induced ring homomorphism `Γ(X, U) ⟶ Γ(G, f ⁻¹ᵁ U)` is finite. -/
theorem finite_app_of_isFinite_morphismRestrict {G X : AlgebraicGeometry.Scheme} (f : G ⟶ X)
    {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (hfin : AlgebraicGeometry.IsFinite (AlgebraicGeometry.morphismRestrict f U)) :
    RingHom.Finite (f.app U).hom := by
  have : IsAffine U := hU
  have : IsFinite (f ∣_ U) := hfin
  have h : RingHom.Finite ((f ∣_ U).appTop).hom := Scheme.Hom.finite_appTop (f ∣_ U)
  have key : (f ∣_ U).appTop = U.topIso.hom ≫ f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    simp [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
  rw [key] at h
  exact (RingHom.RespectsIso.cancel_right_isIso RingHom.finite_respectsIso (f.app U)
      (f ⁻¹ᵁ U).topIso.inv).mp
    ((RingHom.RespectsIso.cancel_left_isIso RingHom.finite_respectsIso U.topIso.hom
      (f.app U ≫ (f ⁻¹ᵁ U).topIso.inv)).mp h)

end Work.Domain.Engine
