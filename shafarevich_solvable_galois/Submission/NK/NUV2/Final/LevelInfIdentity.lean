import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.NUV2.Final.Descent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level inflation map is the ambient inflation

`NK.NUV2.Final.levelInfMap_comp_levelDescentIso`: the Galois-descent isomorphism
`levelDescentIso N` followed by the level inflation map `levelInfMap` (from the fixed field `L^N`
into `L`) is the ambient inflation `groupCohomology.infNatTrans ℤ N 2`.  Hence the level inflation
map is injective (Hilbert 90 for `L/L^N`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Representation

namespace NK.NUV2.Final

section Ident

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- The restriction to the fixed field of a normal subgroup is the descent of the quotient map. -/
theorem restrictNormalHom_fixedField_eq (N : Subgroup (L ≃ₐ[F] L)) [N.Normal] :
    (AlgEquiv.restrictNormalHom (K₁ := L) (E := ↥(IntermediateField.fixedField N)))
      = (IsGalois.normalAutEquivQuotient N).toMonoidHom.comp (QuotientGroup.mk' N) := by
  apply MonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro a
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  show ((AlgEquiv.restrictNormalHom (K₁ := L) (E := ↥(IntermediateField.fixedField N))) σ) a
    = ((IsGalois.normalAutEquivQuotient N) (↑σ)) a
  rw [IsGalois.normalAutEquivQuotient_apply]

/-- The composition of the inverse of the quotient iso with the restriction is the quotient map. -/
theorem normalAutEquivQuotient_symm_comp (N : Subgroup (L ≃ₐ[F] L)) [N.Normal] :
    (IsGalois.normalAutEquivQuotient N).symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom (K₁ := L) (E := ↥(IntermediateField.fixedField N)))
      = QuotientGroup.mk' N := by
  rw [restrictNormalHom_fixedField_eq N]
  ext σ
  simp

end Ident

section Main

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- **The identification of the level inflation with the ambient inflation.** -/
theorem levelInfMap_comp_levelDescentIso (N : Subgroup (L ≃ₐ[F] L)) [N.Normal] :
    (levelDescentIso N).hom ≫
        (NK.NUV2.RouteD.levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N)) (L := L))
      = (groupCohomology.infNatTrans ℤ N 2).app (Rep.ofAlgebraAutOnUnits F L) := by
  haveI : IsGalois F ↥(IntermediateField.fixedField N) := IsGalois.of_fixedField_normal_subgroup N
  haveI : Normal F ↥(IntermediateField.fixedField N) := inferInstance
  rw [levelDescentIso, Iso.trans_hom, Functor.mapIso_hom, groupCohomology.mapIso_hom,
    NK.NUV2.RouteD.levelInfMap]
  simp only [groupCohomology.functor_map]
  rw [Category.assoc]
  rw [← groupCohomology.map_comp]
  rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr (f := (MonoidHom.id ((L ≃ₐ[F] L) ⧸ N)).comp
      ((IsGalois.normalAutEquivQuotient N).symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom (K₁ := L) (E := ↥(IntermediateField.fixedField N)))))
    (g := QuotientGroup.mk' N) ?_ ?_ 2
  · rw [← MonoidHom.comp_assoc, MonoidHom.id_comp, normalAutEquivQuotient_symm_comp N]
  · apply LinearMap.ext
    intro x
    simp only [Rep.hom_comp_toLinearMap, LinearMap.comp_apply, Rep.resMap_hom_toLinearMap,
      Rep.hom_ofHom, NK.NUV2.RouteD.unitsInclCoeff_toLinearMap,
      NK.NUV2.RouteD.unitsInclLinearMap_apply, LinearMap.id_apply]
    show Additive.ofMul (Units.map (algebraMap ↥(IntermediateField.fixedField N) L).toMonoidHom
        (((Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv
          N) x) : (↥(IntermediateField.fixedField N))ˣ))
      = (Submodule.subtype _) (x : Representation.invariants
          (((Rep.ofAlgebraAutOnUnits F L).ρ).comp N.subtype))
    rw [Commons.NumberTheory.NumberField.Completion.NatCardP9.units_map_unitsInvLinearEquiv]
    rfl

/-- **Injectivity of the level inflation map** (Hilbert 90 for `L/L^N`). -/
theorem levelInfMap_injective (N : Subgroup (L ≃ₐ[F] L)) [N.Normal] :
    Function.Injective ⇑(NK.NUV2.RouteD.levelInfMap (F := F)
      (M := ↥(IntermediateField.fixedField N)) (L := L)).hom := by
  haveI : IsGalois F ↥(IntermediateField.fixedField N) := IsGalois.of_fixedField_normal_subgroup N
  haveI : Normal F ↥(IntermediateField.fixedField N) := inferInstance
  have hinf : Function.Injective ⇑((groupCohomology.infNatTrans ℤ N 2).app
      (Rep.ofAlgebraAutOnUnits F L)).hom :=
    Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1 N _
      (Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units N)
  set e := levelDescentIso N with he
  have hmain : NK.NUV2.RouteD.levelInfMap (F := F)
      (M := ↥(IntermediateField.fixedField N)) (L := L)
      = e.inv ≫ (groupCohomology.infNatTrans ℤ N 2).app (Rep.ofAlgebraAutOnUnits F L) := by
    rw [← Category.id_comp (NK.NUV2.RouteD.levelInfMap (F := F)
        (M := ↥(IntermediateField.fixedField N)) (L := L)),
      ← Iso.inv_hom_id e, Category.assoc]
    rw [he] at *
    rw [levelInfMap_comp_levelDescentIso]
  rw [hmain]
  intro a b hab
  rw [ModuleCat.comp_apply] at hab
  have h2 : e.inv a = e.inv b := hinf hab
  have h4 : e.hom (e.inv a) = e.hom (e.inv b) := congrArg (fun z => e.hom z) h2
  simpa only [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply] using h4

end Main

end NK.NUV2.Final
