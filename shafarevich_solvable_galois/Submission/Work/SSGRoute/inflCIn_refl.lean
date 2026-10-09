import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.extHMap_id
import Submission.Work.SSGRoute.classIncl_isCanonical
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
import Submission.Work.SSGRoute.phi1_level_naturality
import Submission.Work.SSGRoute.phi1_classIncl_compat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `inflCIn (le_refl L) = id`: the `map_self` axiom for the class-group level system

This is the analogue, for the coefficient module `C_L` (idèle class groups), of
`Work.SSGRoute.inflTrivIn_refl` for a trivial coefficient module: the inflation map of
`H^n(Gal(L/k), C_L)` along the *self* level inclusion `L ⊆ L` is the identity.  It supplies the
`map_self` axiom of the level system of `Work.SSGRoute.phi1_mono_step_in` when the coefficients are
idèle class groups rather than `𝔽_p`.

`inflCIn (le_refl L)` unfolds to `extHMap (galRes k L L) (classIncl k L L)`, and the whole content
sits in the coefficient map `classIncl k L L : C_L → C_L`: it is the canonical inclusion of idèle
class groups chosen by `classIncl`, and the canonical inclusion of `C_L` into itself is the
identity.  Formally:

* `galRes k L L = AlgEquiv.restrictNormalHom L = MonoidHom.id` (`AlgEquiv.restrictNormalHom_id`);
* the two presentations `Rep.res (galRes k L L) (classesK k L)` and `classesK k L` of `C_L` are
  canonically identified (`hobj`, proved by `dsimp only [Rep.res, Rep.resFunctor]` and the
  representation equality), and `eqToHom hobj` is the identity on underlying elements (`htr`);
* hence `classIncl k L L = eqToHom hobj` by *uniqueness* of the canonical inclusion
  (`Work.SSGRoute.isCanonicalClassIncl_unique`), using `IsCanonicalClassIncl` with the idèle map
  `𝕀_L → 𝕀_L` given by `u = id`, `φ = id` (its `w`-component is the local embedding, which is the
  identity by `Work.SSGRoute.localAlgebraMapUnits_self`);
* finally `extHMap` is computed with the natural transformation `θ : Rep.resFunctor (galRes k L L) ⟶ 𝟭`
  given by the functor equality `Rep.resFunctor (galRes k L L) = 𝟭`:
  `Abelian.Ext.mapExactFunctor` with `θ` (`Work.SSGRoute.ext_mapExactFunctor_naturality_aux`) turns
  `extHMap (eqToHom hobj)` into the identity, and the outer `mk₀ (unitRes ·)` collapses because
  `unitRes` is the identity on the trivial coefficient module.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory SSGRoute.PTExt NK.GlobalCFT
open NumberField

namespace Work.SSGRoute

/-- v4.35 port helper: the canonical inclusion `C_E → C_E` is the identity `eqToHom`, proved once
for a general number field `E` (so the kernel checks the idèle clause generically, cheaply). -/
theorem classIncl_self_eq_eqToHom (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E]
    [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
    (hobj : Rep.res (SSGRoute.PTExt.galRes k E E) (SSGRoute.PTExt.classesK k E)
      = SSGRoute.PTExt.classesK k E) :
    SSGRoute.PTExt.classIncl k E E = eqToHom hobj := by
  have hu : ∀ w : Place E, Place.LiesOver (K := E) (L := E) w w := by
    intro w
    rcases w with w | q
    · exact Place.liesOver_ofInfinite
        ((Norm.liesOver_iff_comap_eq (K := E) (L := E) w w).mpr
          (NumberField.InfinitePlace.comap_id w))
    · exact Place.liesOver_ofFinite
        ((Norm.liesOver_iff_under_eq q.asIdeal q.asIdeal).mpr (by
          rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id]))
  have htr : ∀ z : ↥(Rep.res (SSGRoute.PTExt.galRes k E E) (SSGRoute.PTExt.classesK k E)),
      (Rep.Hom.hom (eqToHom hobj)) z = z := by
    intro z
    rw [Rep.eqToHom_hom_apply]
    exact eq_of_heq (rec_heq_of_heq hobj (HEq.refl z))
  apply isCanonicalClassIncl_unique
  · exact classIncl_isCanonical k E E
  · refine ⟨id, hu, MonoidHom.id (Idele E), ?_, ?_⟩
    · intro x w
      show x w = Place.localAlgebraMapUnits w w (hu w) (x w)
      exact (localAlgebraMapUnits_self E w (hu w) (x w)).symm
    · intro x
      rw [MonoidHom.id_apply]
      exact htr _

theorem inflCIn_refl {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {L : IntermediateField K Ω} [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    {n : ℕ} (y : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) n) :
    SSGRoute.PTExt.inflCIn (k := k) (le_refl L) y = y := by
  unfold SSGRoute.PTExt.inflCIn SSGRoute.PTExt.inflC
  change SSGRoute.PTExt.extHMap (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))
    (SSGRoute.PTExt.classIncl k ↥L ↥L) y = y
  have hg : AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L)
      = MonoidHom.id (↥L ≃ₐ[k] ↥L) := AlgEquiv.restrictNormalHom_id k ↥L
  have hobj : Rep.res (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))
      (SSGRoute.PTExt.classesK k ↥L) = SSGRoute.PTExt.classesK k ↥L := by
    have h : (SSGRoute.PTExt.classesK k ↥L).ρ.comp
          (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))
        = (SSGRoute.PTExt.classesK k ↥L).ρ := by rw [hg]; rfl
    dsimp only [Rep.res, Rep.resFunctor]
    rw [h]
  have hu : ∀ w : Place ↥L, Place.LiesOver (K := ↥L) (L := ↥L) w w := by
    intro w
    rcases w with w | q
    · exact Place.liesOver_ofInfinite
        ((Norm.liesOver_iff_comap_eq (K := ↥L) (L := ↥L) w w).mpr
          (NumberField.InfinitePlace.comap_id w))
    · exact Place.liesOver_ofFinite
        ((Norm.liesOver_iff_under_eq q.asIdeal q.asIdeal).mpr (by
          rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id]))
  have htr : ∀ z : ↥(Rep.res (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))
      (SSGRoute.PTExt.classesK k ↥L)),
      (Rep.Hom.hom (eqToHom hobj)) z = z := by
    intro z
    rw [Rep.eqToHom_hom_apply]
    exact eq_of_heq (rec_heq_of_heq hobj (HEq.refl z))
  have hclass : SSGRoute.PTExt.classIncl k ↥L ↥L = eqToHom hobj :=
    classIncl_self_eq_eqToHom k ↥L hobj
  rw [hclass]
  have hF : Rep.resFunctor (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))
      = 𝟭 (Rep Coeff (↥L ≃ₐ[k] ↥L)) := by rw [hg]; rfl
  let θ : Rep.resFunctor (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L)) ⟶ 𝟭 _ := eqToHom hF
  have hθA : θ.app (SSGRoute.PTExt.classesK k ↥L) = eqToHom hobj := by
    show (eqToHom hF).app (SSGRoute.PTExt.classesK k ↥L) = eqToHom hobj
    rw [CategoryTheory.eqToHom_app]
  have hθX : θ.app (SSGRoute.PTExt.unitRep (↥L ≃ₐ[k] ↥L))
      = 𝟙 (SSGRoute.PTExt.unitRep (↥L ≃ₐ[k] ↥L)) := by
    show (eqToHom hF).app (SSGRoute.PTExt.unitRep (↥L ≃ₐ[k] ↥L)) = 𝟙 _
    rw [CategoryTheory.eqToHom_app]
    exact CategoryTheory.eqToHom_refl _ _
  have hnat := ext_mapExactFunctor_naturality_aux
    (Rep.resFunctor (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))) θ n
    (SSGRoute.PTExt.unitRep (↥L ≃ₐ[k] ↥L)) (SSGRoute.PTExt.classesK k ↥L) y
  have hV : (Abelian.Ext.mk₀ (θ.app (SSGRoute.PTExt.unitRep (↥L ≃ₐ[k] ↥L)))).comp y
      (zero_add n) = y := by
    rw [hθX]
    exact Abelian.Ext.mk₀_id_comp y
  have hw : (Abelian.Ext.mk₀ (unitRes (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L)))).comp
      ((y.mapExactFunctor (Rep.resFunctor (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L)))).comp
        (Abelian.Ext.mk₀ (eqToHom hobj)) (add_zero n)) (zero_add n)
      = (y.mapExactFunctor (Rep.resFunctor (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L)))).comp
        (Abelian.Ext.mk₀ (eqToHom hobj)) (add_zero n) := by
    rw [show unitRes (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))
        = 𝟙 (SSGRoute.PTExt.unitRep (↥L ≃ₐ[k] ↥L)) from rfl]
    exact Abelian.Ext.mk₀_id_comp _
  unfold SSGRoute.PTExt.extHMap SSGRoute.PTExt.extRes
  refine hw.trans ?_
  rw [← hθA]
  exact hnat.trans hV

end Work.SSGRoute

