import Mathlib
import Submission.NK.NUV2.RouteD.LevelInf
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian

/-!
# The Galois-descent isomorphism for the level cohomology

For a finite Galois extension `F ⊆ L` and a normal subgroup `N ≤ Gal(L/F)` with fixed field
`M = L^N`, the cohomology `H²(G⧸N, (Lˣ)^N)` of the quotient group with coefficients in the
invariants is canonically the *level cohomology* `H²(Gal(M/F), Mˣ)` of the fixed field.  This file
provides the isomorphism as a *transparent* `Iso` of `ℤ`-modules (so that it can be manipulated in
diagram chases, unlike the `Nonempty`-valued version
`Commons…addEquiv_groupCohomology_two_quotientToInvariants_units`).

The main result of the file is the identification of the *level inflation map* with the ambient
inflation: `levelDescentIso ≫ levelInfMap = infNatTrans N`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Representation

namespace NK.NUV2.RouteD

universe u

section Descent

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- The representation isomorphism underlying the Galois descent: the invariants `(Lˣ)^N` of the
units of `L` under `N` are the units of the fixed field `L^N` (with the `G⧸N`-action). -/
noncomputable def unitsDescentIso (N : Subgroup (L ≃ₐ[F] L)) [N.Normal] :
    (Rep.ofAlgebraAutOnUnits F L).quotientToInvariants N ≅
      Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
        (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)) :=
  { hom := Rep.ofHom ⟨(Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv
        N).toLinearMap, fun g => by
      apply LinearMap.ext; intro x
      exact Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv_equivariant
        N g x⟩
    inv := Rep.ofHom ⟨(Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv
        N).symm.toLinearMap, fun g => by
      apply LinearMap.ext; intro y
      show (Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N).symm
          ((Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
            (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N))).ρ g y)
        = ((Rep.ofAlgebraAutOnUnits F L).quotientToInvariants N).ρ g
            ((Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv
              N).symm y)
      conv_lhs => rw [show y = (Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N)
          ((Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N).symm y) from
        (LinearEquiv.apply_symm_apply _ y).symm]
      rw [(Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv_equivariant
        N g ((Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N).symm y)).symm]
      rw [LinearEquiv.symm_apply_apply]⟩
    hom_inv_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rw [Rep.hom_comp_toLinearMap]
      simp only [Rep.hom_ofHom, LinearMap.comp_apply]
      exact LinearEquiv.symm_apply_apply
        (Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N) x
    inv_hom_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rw [Rep.hom_comp_toLinearMap]
      simp only [Rep.hom_ofHom, LinearMap.comp_apply]
      exact LinearEquiv.apply_symm_apply
        (Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N) x }

/-- **The Galois-descent isomorphism of level cohomology**: `H²(G⧸N, (Lˣ)^N) ≅ H²(Gal(L^N/F), (L^N)ˣ)`.
This is the transparent form of
`Commons…addEquiv_groupCohomology_two_quotientToInvariants_units`. -/
noncomputable def levelDescentIso (N : Subgroup (L ≃ₐ[F] L)) [N.Normal] :
    groupCohomology ((Rep.ofAlgebraAutOnUnits F L).quotientToInvariants N) 2 ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)) 2 :=
  ((groupCohomology.functor ℤ ((L ≃ₐ[F] L) ⧸ N) 2).mapIso (unitsDescentIso N)) ≪≫
    (groupCohomology.mapIso (G := (L ≃ₐ[F] L) ⧸ N)
      (H := ↥(IntermediateField.fixedField N) ≃ₐ[F] ↥(IntermediateField.fixedField N))
      (A := Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N))
      (B := Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
        (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)))
      (IsGalois.normalAutEquivQuotient N) (LinearEquiv.refl ℤ
        (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)).V) (by intro g; rfl) 2)

end Descent

end NK.NUV2.RouteD

namespace NK.NUV2.RouteD

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

end NK.NUV2.RouteD

namespace NK.NUV2.RouteD

section Main

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- **The identification of the level inflation with the ambient inflation.**

For a finite Galois extension `F ⊆ L` and a normal subgroup `N ≤ Gal(L/F)` with fixed field
`M = L^N`, the composite of the Galois-descent isomorphism
`levelDescentIso : H²(G⧸N, (Lˣ)^N) ≅ H²(Gal(M/F), Mˣ)` with the level inflation map
`levelInfMap : H²(Gal(M/F), Mˣ) → H²(Gal(L/F), Lˣ)` is the ambient inflation
`infNatTrans N : H²(G⧸N, (Lˣ)^N) → H²(Gal(L/F), Lˣ)`.

This is the statement that the intrinsic level cohomology agrees with the ambient description; it
is proved by rewriting both sides as single `groupCohomology.map`s and applying `map_congr` (the
coefficient equality is `NatCardP9.units_map_unitsInvLinearEquiv`). -/
theorem levelDescentIso_hom_comp_levelInfMap (N : Subgroup (L ≃ₐ[F] L)) [N.Normal] :
    (levelDescentIso N).hom ≫ levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N)) (L := L)
      = (groupCohomology.infNatTrans ℤ N 2).app (Rep.ofAlgebraAutOnUnits F L) := by
  haveI : IsGalois F ↥(IntermediateField.fixedField N) := IsGalois.of_fixedField_normal_subgroup N
  haveI : Normal F ↥(IntermediateField.fixedField N) := inferInstance
  rw [levelDescentIso, Iso.trans_hom, Functor.mapIso_hom, groupCohomology.mapIso_hom, levelInfMap]
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
      Rep.hom_ofHom, unitsInclCoeff_toLinearMap, unitsInclLinearMap_apply,
      LinearMap.id_apply]
    show Additive.ofMul (Units.map (algebraMap ↥(IntermediateField.fixedField N) L).toMonoidHom
        (((Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv
          N) x) : (↥(IntermediateField.fixedField N))ˣ))
      = (Submodule.subtype _) (x : Representation.invariants
          (((Rep.ofAlgebraAutOnUnits F L).ρ).comp N.subtype))
    rw [Commons.NumberTheory.NumberField.Completion.NatCardP9.units_map_unitsInvLinearEquiv]
    rfl

end Main

end NK.NUV2.RouteD

namespace NK.NUV2.RouteD

section InjectiveRange

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- **Injectivity and range of the level inflation map.**

For a finite Galois extension `F ⊆ L`, a normal subgroup `N ≤ Gal(L/F)` with fixed field `M = L^N`,
the level inflation `H²(Gal(M/F), Mˣ) → H²(Gal(L/F), Lˣ)` is injective with image the `N.index`-torsion
of `H²(Gal(L/F), Lˣ)`.  This follows from the identification
`levelDescentIso_hom_comp_levelInfMap` with the ambient inflation
(`infNatTrans_units_injective_range`) and the fact that the Galois-descent isomorphism is a
bijection. -/
theorem levelInfMap_injective_range (N : Subgroup (L ≃ₐ[F] L)) [N.Normal]
    (hfin : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2))
    (hcard : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) = Nat.card (L ≃ₐ[F] L))
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2))
    (hcardK : Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)) 2) = N.index) :
    Function.Injective ⇑((levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N))
        (L := L)).hom) ∧
      LinearMap.range ((levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N))
          (L := L)).hom) = LinearMap.ker ((N.index : ℤ) • LinearMap.id) := by
  haveI : IsGalois F ↥(IntermediateField.fixedField N) := IsGalois.of_fixedField_normal_subgroup N
  haveI : Normal F ↥(IntermediateField.fixedField N) := inferInstance
  have hinf := infNatTrans_units_injective_range (B := F) (E := L) N hfin hcard u hu hcardK
  have hmain : levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N)) (L := L)
      = (levelDescentIso N).inv ≫ (groupCohomology.infNatTrans ℤ N 2).app
          (Rep.ofAlgebraAutOnUnits F L) := by
    calc levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N)) (L := L)
        = 𝟙 _ ≫ levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N)) (L := L) := by
          rw [Category.id_comp]
      _ = ((levelDescentIso N).inv ≫ (levelDescentIso N).hom) ≫
            levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N)) (L := L) := by
          rw [Iso.inv_hom_id]
      _ = (levelDescentIso N).inv ≫ ((levelDescentIso N).hom ≫
            levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N)) (L := L)) := by
          rw [Category.assoc]
      _ = (levelDescentIso N).inv ≫ (groupCohomology.infNatTrans ℤ N 2).app
            (Rep.ofAlgebraAutOnUnits F L) := by
          rw [levelDescentIso_hom_comp_levelInfMap]
  refine ⟨?_, ?_⟩
  · rw [hmain, ModuleCat.hom_comp]
    refine hinf.1.comp (fun x y h => ?_)
    have h' : (ModuleCat.Hom.hom ((levelDescentIso N).inv ≫ (levelDescentIso N).hom)) x
        = (ModuleCat.Hom.hom ((levelDescentIso N).inv ≫ (levelDescentIso N).hom)) y := by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, h]
    simpa using h'
  · rw [hmain, ModuleCat.hom_comp, LinearMap.range_comp]
    have htop : LinearMap.range (ModuleCat.Hom.hom (levelDescentIso N).inv) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro x
      refine ⟨(ModuleCat.Hom.hom (levelDescentIso N).hom) x, ?_⟩
      have h' : (ModuleCat.Hom.hom ((levelDescentIso N).hom ≫ (levelDescentIso N).inv)) x
          = (ModuleCat.Hom.hom (𝟙 (groupCohomology
              ((Rep.ofAlgebraAutOnUnits F L).quotientToInvariants N) 2))) x := by
        rw [Iso.hom_inv_id]
      simpa using h'
    rw [htop, Submodule.map_top]
    exact hinf.2

end InjectiveRange

end NK.NUV2.RouteD
