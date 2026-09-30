import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveFacts

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry
universe u

/-- Let `f : X ⟶ Spec K` be a smooth morphism of schemes over a field `K`, and let `U ⊆ X` be
an affine open. Then the ring of sections `Γ(X, U)` is a smooth `K`-algebra, i.e. the canonical
structure map `K ⟶ Γ(Spec K, ⊤) ⟶ Γ(X, U)` is a smooth ring homomorphism.

This is the defining property of smoothness of `f` applied to the affine opens `⊤ ⊆ Spec K` and
`U ⊆ X`, composed with the (bijective, hence smooth) canonical isomorphism `K ≅ Γ(Spec K, ⊤)`. -/
theorem smooth_sections {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] {U : X.Opens} (hU : IsAffineOpen U) :
    ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Smooth := by
  -- the induced map on sections `Γ(Spec K, ⊤) ⟶ Γ(X, U)` is smooth
  have h1 : RingHom.Smooth (f.appLE ⊤ U le_top).hom :=
    f.smooth_appLE (isAffineOpen_top _) hU le_top
  -- `K ⟶ Γ(Spec K, ⊤)` is an isomorphism, hence smooth
  have h2 : RingHom.Smooth ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  -- composition of smooth ring homomorphisms is smooth
  exact RingHom.Smooth.comp h2 h1

end Work.CurveFacts
