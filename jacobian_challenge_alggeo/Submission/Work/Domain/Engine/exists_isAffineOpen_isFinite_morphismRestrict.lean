import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Domain.Engine

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a finite morphism to a smaller open of its target: if `f` is finite over `V` and
`U ≤ V`, then `f` is finite over `U`.

This is the only place where the `IsFinite`-instance for `f ∣_ U` (a property local at the target)
is used with a transparency setting that lets the instance be found. -/
private lemma isFinite_morphismRestrict_of_le {G X : AlgebraicGeometry.Scheme} (f : G ⟶ X)
    {V : X.Opens} (hV : AlgebraicGeometry.IsFinite (AlgebraicGeometry.morphismRestrict f V))
    (U : X.Opens) (hUV : U ≤ V) :
    AlgebraicGeometry.IsFinite (AlgebraicGeometry.morphismRestrict f U) := by
  let V' : V.toScheme.Opens := V.ι ⁻¹ᵁ U
  have himg : V.ι ''ᵁ V' = U := by
    change V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hUV
  have h1 : IsFinite (f ∣_ V ∣_ V') :=
    IsZariskiLocalAtTarget.restrict (P := @IsFinite) hV V'
  have hiso : Arrow.mk (f ∣_ V ∣_ V') ≅ Arrow.mk (f ∣_ U) :=
    morphismRestrictRestrict f V V' ≪≫ morphismRestrictEq f himg
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) hiso).mp h1

theorem exists_isAffineOpen_isFinite_morphismRestrict {G X : AlgebraicGeometry.Scheme} (f : G ⟶ X)
    [AlgebraicGeometry.IsProper f] (x : X) (hfin : (f ⁻¹' {x}).Finite) :
    ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧ x ∈ U ∧
      AlgebraicGeometry.IsFinite (AlgebraicGeometry.morphismRestrict f U) := by
  -- Zariski's main theorem (Stacks 02UP): a proper morphism with finite fibre over `x` is finite
  -- over some open neighbourhood `V` of `x`.
  obtain ⟨V, hxV, hVfin⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hfin
  -- Choose an affine open `U` with `x ∈ U ⊆ V` (affine opens form a basis).
  obtain ⟨_, ⟨U : X.Opens, hUaff, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.2
  exact ⟨U, hUaff, hxU, isFinite_morphismRestrict_of_le f hVfin U hUV⟩

end Work.Domain.Engine
