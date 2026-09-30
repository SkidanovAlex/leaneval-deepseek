import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Domain.Engine

open CategoryTheory AlgebraicGeometry

/-- If the structure map on sections over an affine open `U` is surjective, the morphism is
surjective, and `U` is reduced, then the restriction of the morphism to `U` is an isomorphism.

The mathematical content: `f.app U` is the ring map `Γ(X,U) → Γ(G, f⁻¹U)`, which is surjective.
The restricted morphism `f ∣_ U` is then a closed immersion (being surjective on sections) whose
underlying map is surjective; since `U` is affine and reduced, the associated quotient of `Γ(X,U)`
has to be trivial, so `f.app U` is injective as well, i.e. an isomorphism, and `f ∣_ U` is one
because both source and target are affine. -/
theorem isIso_morphismRestrict_of_surjective_app {G X : AlgebraicGeometry.Scheme} (f : G ⟶ X)
    {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (hU' : AlgebraicGeometry.IsAffineOpen ((TopologicalSpace.Opens.map f.base).obj U))
    [AlgebraicGeometry.IsReduced (U.toScheme)]
    (h : Function.Surjective ((f.app U).hom))
    (hsurj : AlgebraicGeometry.Surjective (AlgebraicGeometry.morphismRestrict f U)) :
    CategoryTheory.IsIso (AlgebraicGeometry.morphismRestrict f U) := by
  -- Both `U` and `f ⁻¹ᵁ U` are affine, so the canonical maps to their spectra are isomorphisms.
  have hUiso : IsIso U.toSpecΓ := by
    have hUa : IsAffine (U.toScheme) := hU
    rw [Scheme.Opens.toSpecΓ]
    infer_instance
  have hU'iso : IsIso (f ⁻¹ᵁ U).toSpecΓ := by
    have hU'a : IsAffine ((f ⁻¹ᵁ U).toScheme) := hU'
    rw [Scheme.Opens.toSpecΓ]
    infer_instance
  -- The naturality square relating `f.app U` and `f ∣_ U` via the affine identifications.
  have hsq' : (asIso ((f ⁻¹ᵁ U).toSpecΓ)).hom ≫ Spec.map (f.app U)
      = (f ∣_ U) ≫ (asIso U.toSpecΓ).hom := by
    rw [asIso_hom, asIso_hom]
    exact Scheme.Opens.toSpecΓ_naturality f U
  have heq : Spec.map (f.app U)
      = (asIso ((f ⁻¹ᵁ U).toSpecΓ)).inv ≫ (f ∣_ U) ≫ (asIso U.toSpecΓ).hom := by
    rw [← hsq', Iso.inv_hom_id_assoc]
  -- Surjectivity of `f ∣_ U` transfers to surjectivity of `Spec.map (f.app U)`.
  have hsurjSm : Function.Surjective ⇑(Spec.map (f.app U)) := by
    rw [heq]
    intro y
    obtain ⟨a, ha⟩ := Scheme.Hom.surjective (asIso U.toSpecΓ).hom y
    obtain ⟨b, hb⟩ := hsurj.surj a
    obtain ⟨c, hc⟩ := Scheme.Hom.surjective (asIso ((f ⁻¹ᵁ U).toSpecΓ)).inv b
    exact ⟨c, by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hc, hb, ha]⟩
  have hcomap : Function.Surjective (PrimeSpectrum.comap ((f.app U).hom)) := by
    have hbase : ⇑(Spec.map (f.app U)) = PrimeSpectrum.comap ((f.app U).hom) := by
      rw [Spec.map_base]; rfl
    rw [← hbase]; exact hsurjSm
  -- `Γ(X, U)` is reduced because `U` is an affine reduced scheme.
  have hred : _root_.IsReduced Γ(X, U) := by
    have hredSpec : IsReduced (Spec Γ(X, U)) := isReduced_of_isOpenImmersion hU.isoSpec.inv
    exact (affine_isReduced_iff Γ(X, U)).mp hredSpec
  have hnil : nilradical Γ(X, U) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    exact (mem_nilradical.mp hx).eq_zero
  -- Surjectivity of the comap forces the kernel of `f.app U` inside the nilradical, which is zero.
  have hker_le : RingHom.ker ((f.app U).hom) ≤ nilradical Γ(X, U) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ((f.app U).hom)).mp
      hcomap.denseRange
  have hkerbot : RingHom.ker ((f.app U).hom) = ⊥ := le_bot_iff.mp (hker_le.trans (le_of_eq hnil))
  have hinj : Function.Injective ((f.app U).hom) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr hkerbot
  have hiso : IsIso (f.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hinj, h⟩
  have hSpec : IsIso (Spec.map (f.app U)) := inferInstance
  -- Conclude for `f ∣_ U` itself.
  have hg : f ∣_ U = (asIso ((f ⁻¹ᵁ U).toSpecΓ)).hom ≫ Spec.map (f.app U)
      ≫ (asIso U.toSpecΓ).inv := by
    rw [← Category.assoc, hsq', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hg]
  infer_instance

end Work.Domain.Engine
