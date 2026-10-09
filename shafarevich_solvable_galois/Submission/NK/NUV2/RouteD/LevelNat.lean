import Mathlib
import Submission.NK.NUV2.RouteD.LevelInf
import Submission.Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_topAlgEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of the level cohomology along an algebra isomorphism, and its naturality

For two field extensions `F ⊆ E` and `F ⊆ E'` and an `F`-algebra isomorphism `ψ : E ≃ₐ[F] E'`, the
second group cohomology of the units is transported along `ψ`:

`unitsCohIso ψ : H²(Gal(E/F), Eˣ) ≅ H²(Gal(E'/F), E'ˣ)`.

This is the *transparent* form of the (opaque) `Nonempty`-valued statement
`Commons…addEquiv_groupCohomology_two_units_topAlgEquiv`.

The main result of the file is the *naturality* of this transport with respect to the level
inflation map: if `ψ` is compatible with the inclusions of `E` and `E'` into a common field `E''`,
then transporting the source of `levelInfMap` along `ψ` does not change the inflation map.  This is
what makes the level inflation map, and hence the whole level theory, well defined on the Galois
correspondence.
-/

open CategoryTheory Representation
open Additive

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.NUV2.RouteD

universe u

/-- **The coefficient morphism** of the transport of `H²` of the units along `ψ : E ≃ₐ[F] E'`. -/
noncomputable def unitsCohCoeff {F E E' : Type} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] (ψ : E ≃ₐ[F] E') :
    Rep.res (AlgEquiv.autCongr ψ).symm.toMonoidHom (Rep.ofAlgebraAutOnUnits F E) ⟶
      Rep.ofAlgebraAutOnUnits F E' :=
  Rep.ofHom
    { toLinearMap := ((Commons.NumberTheory.NumberField.Completion.unitsAddEquiv ψ).toLinearEquiv
        (fun c x => map_zsmul _ c x) : Additive Eˣ →ₗ[ℤ] Additive E'ˣ)
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro u
        have h := Commons.NumberTheory.NumberField.Completion.unitsAddEquiv_conj ψ
          ((AlgEquiv.autCongr ψ).symm g) u
        rw [MulEquiv.apply_symm_apply] at h
        exact h }

/-- The coefficient morphism acts as the additive equivalence of units induced by `ψ`. -/
theorem unitsCohCoeff_apply {F E E' : Type} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] (ψ : E ≃ₐ[F] E') (u : Additive Eˣ) :
    (Rep.Hom.hom (unitsCohCoeff ψ)).toLinearMap u
      = Commons.NumberTheory.NumberField.Completion.unitsAddEquiv ψ u := rfl

/-- **Transport of `H²` of the units along an `F`-algebra isomorphism `ψ : E ≃ₐ[F] E'`.** -/
noncomputable def unitsCohIso {F E E' : Type} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] (ψ : E ≃ₐ[F] E') :
    groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2 ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits F E') 2 :=
  groupCohomology.mapIso (A := Rep.ofAlgebraAutOnUnits F E') (B := Rep.ofAlgebraAutOnUnits F E)
    (AlgEquiv.autCongr ψ)
    ((Commons.NumberTheory.NumberField.Completion.unitsAddEquiv ψ).toLinearEquiv
      (fun c x => map_zsmul _ c x))
    (by
      intro g
      apply LinearMap.ext
      intro u
      exact Commons.NumberTheory.NumberField.Completion.unitsAddEquiv_conj ψ g u) 2

end NK.NUV2.RouteD

namespace NK.NUV2.RouteD

section Helpers

variable {F E E' : Type} [Field F] [Field E] [Field E'] [Algebra F E] [Algebra F E']
  (ψ : E ≃ₐ[F] E')

/-- The conjugated inverse acts as `ψ⁻¹ ∘ τ ∘ ψ`. -/
theorem autCongr_symm_apply_apply (τ : E' ≃ₐ[F] E') (x : E) :
    ((AlgEquiv.autCongr ψ).symm.toMonoidHom τ) x = ψ.symm (τ (ψ x)) := by
  show ((AlgEquiv.autCongr ψ).symm τ) x = ψ.symm (τ (ψ x))
  rw [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_symm]

end Helpers

section Helpers2

variable {F E E' E'' : Type} [Field F] [Field E] [Field E'] [Field E'']
  [Algebra F E] [Algebra F E'] [Algebra F E''] [Algebra E E''] [Algebra E' E'']
  (ψ : E ≃ₐ[F] E') (hψ : ∀ x : E, algebraMap E' E'' (ψ x) = algebraMap E E'' x)

/-- The compatibility of `ψ` with the inclusions, inverted. -/
theorem algebraMap_symm_apply (ψ : E ≃ₐ[F] E')
    (hψ : ∀ x : E, algebraMap E' E'' (ψ x) = algebraMap E E'' x) {y : E'} :
    algebraMap E E'' (ψ.symm y) = algebraMap E' E'' y := by
  have h := hψ (ψ.symm y)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

end Helpers2

end NK.NUV2.RouteD

namespace NK.NUV2.RouteD

section Main

variable {F E E' E'' : Type} [Field F] [Field E] [Field E'] [Field E'']
  [Algebra F E] [Algebra F E'] [Algebra F E''] [Algebra E E''] [Algebra E' E'']
  [IsScalarTower F E E''] [IsScalarTower F E' E''] [Normal F E] [Normal F E'] [Normal F E'']

/-- **Naturality of the transport**: rewriting the source of `levelInfMap` along `ψ` gives back
the same map, provided `ψ` is compatible with the inclusions into `E''`. -/
theorem unitsCohIso_hom_naturality (ψ : E ≃ₐ[F] E') :
    (unitsCohIso ψ).hom
      = groupCohomology.map (AlgEquiv.autCongr ψ).symm.toMonoidHom (unitsCohCoeff ψ) 2 := by
  rw [unitsCohIso, groupCohomology.mapIso_hom]
  refine groupCohomology.map_congr rfl ?_ 2
  apply LinearMap.ext
  intro u
  rfl

/-- **Naturality of the level inflation map under the transport of the source field.**

If `ψ : E ≃ₐ[F] E'` is compatible with the inclusions of `E` and `E'` into `E''`, then transporting
`H²(Gal(E/F), Eˣ)` along `ψ` and then inflating to the level `E''` is the same as inflating
directly. -/
theorem levelInfMap_unitsCohIso (ψ : E ≃ₐ[F] E')
    (hψ : ∀ x : E, algebraMap E' E'' (ψ x) = algebraMap E E'' x) :
    (unitsCohIso ψ).hom ≫ levelInfMap (F := F) (M := E') (L := E'')
      = levelInfMap (F := F) (M := E) (L := E'') := by
  rw [unitsCohIso_hom_naturality]
  show groupCohomology.map (AlgEquiv.autCongr ψ).symm.toMonoidHom (unitsCohCoeff ψ) 2
      ≫ groupCohomology.map (AlgEquiv.restrictNormalHom (K₁ := E'') (E := E'))
          (unitsInclCoeff (F := F) (M := E') (L := E'')) 2
    = groupCohomology.map (AlgEquiv.restrictNormalHom (K₁ := E'') (E := E))
        (unitsInclCoeff (F := F) (M := E) (L := E'')) 2
  rw [← groupCohomology.map_comp
    (f := (AlgEquiv.autCongr ψ).symm.toMonoidHom)
    (g := AlgEquiv.restrictNormalHom (K₁ := E'') (E := E'))
    (φ := unitsCohCoeff ψ)
    (ψ := unitsInclCoeff (F := F) (M := E') (L := E'')) 2]
  refine groupCohomology.map_congr ?_ ?_ 2
  · -- the group homomorphisms agree
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply FaithfulSMul.algebraMap_injective E E''
    show algebraMap E E''
        (((AlgEquiv.autCongr ψ).symm.toMonoidHom.comp
          (AlgEquiv.restrictNormalHom (K₁ := E'') (E := E')) σ) x)
      = algebraMap E E''
          ((AlgEquiv.restrictNormalHom (K₁ := E'') (E := E) σ) x)
    rw [MonoidHom.comp_apply, autCongr_symm_apply_apply ψ, algebraMap_symm_apply ψ hψ]
    rw [show (AlgEquiv.restrictNormalHom (K₁ := E'') (E := E') σ) = σ.restrictNormal E' from rfl,
      show (AlgEquiv.restrictNormalHom (K₁ := E'') (E := E) σ) = σ.restrictNormal E from rfl]
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes, hψ x]
  · -- the coefficient morphisms agree
    rw [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap]
    apply LinearMap.ext
    intro u
    change Additive.ofMul (Units.map (algebraMap E' E'').toMonoidHom
        (Additive.toMul ((Commons.NumberTheory.NumberField.Completion.unitsAddEquiv ψ) (u : Additive Eˣ))))
      = Additive.ofMul (Units.map (algebraMap E E'').toMonoidHom (Additive.toMul (u : Additive Eˣ)))
    congr 1
    apply Units.ext
    exact hψ ↑(Additive.toMul (show Additive (Eˣ) from u))

end Main

end NK.NUV2.RouteD
