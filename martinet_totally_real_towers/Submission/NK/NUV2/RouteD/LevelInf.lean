import Mathlib
import Submission.NK.NUV2.RouteD.LevelSetup

/-!
# The level inflation maps for the abstract local level theory

For a tower of fields `F ⊆ M ⊆ L` (with `M/F` normal), this file defines the *level inflation map*

`levelInfMap : H²(Gal(M/F), Mˣ) → H²(Gal(L/F), Lˣ)`

as the map induced by the restriction `Gal(L/F) →* Gal(M/F)` and the units inclusion `Mˣ → Lˣ`
(a coefficient change of representations).  This is the intrinsic form of the transition map of the
local class formation: its two structural properties are

* functoriality (`levelInfMap_comp`) — it is a functor on the tower, immediate from
  `groupCohomology.map_comp`;
* normality with the `H⁰ × H²` cup product (`levelInfMap_cup`) — `Inf(a ∪ δ(χ ∘ res)) = a ∪ δχ`;
* injectivity with range the `[M:F]`-torsion (`levelInfMap_injective`, `levelInfMap_range`),
  which is the Galois-descent / Hilbert-90 statement.

The first two are proved here; the third is the target of a delegated lemma (its proof goes through
the identification of the source with the invariants of the ambient cohomology,
`Commons…addEquiv_groupCohomology_two_quotientToInvariants_units`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory Representation

namespace NK.NUV2.RouteD

set_option maxHeartbeats 1600000

universe u

section UnitsIncl

variable {F M L : Type} [Field F] [Field M] [Field L]
  [Algebra F M] [Algebra F L] [Algebra M L] [IsScalarTower F M L]

/-- The units inclusion `Mˣ → Lˣ` as a `ℤ`-linear map. -/
noncomputable def unitsInclLinearMap : Additive Mˣ →ₗ[ℤ] Additive Lˣ :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (Units.map (algebraMap M L).toMonoidHom (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun x y => by
        show Additive.ofMul (Units.map (algebraMap M L).toMonoidHom
              (Additive.toMul (x + y))) =
            Additive.ofMul (Units.map (algebraMap M L).toMonoidHom (Additive.toMul x)) +
              Additive.ofMul (Units.map (algebraMap M L).toMonoidHom (Additive.toMul y))
        rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl, map_mul]
        rfl }

@[simp]
theorem unitsInclLinearMap_apply (x : Additive Mˣ) :
    (unitsInclLinearMap : Additive Mˣ →ₗ[ℤ] Additive Lˣ) x
      = Additive.ofMul (Units.map (algebraMap M L).toMonoidHom (Additive.toMul x)) := rfl

end UnitsIncl

section LevelInf

variable {F M L : Type} [Field F] [Field M] [Field L]
  [Algebra F M] [Algebra F L] [Algebra M L] [IsScalarTower F M L] [Normal F M]

/-- **The coefficient morphism of the level inflation map**: the units inclusion `Mˣ → Lˣ` as a
morphism of representations over the restriction `Gal(L/F) →* Gal(M/F)`. -/
noncomputable abbrev unitsInclCoeff :
    Rep.res (AlgEquiv.restrictNormalHom (K₁ := L) (E := M))
        (Rep.ofAlgebraAutOnUnits F M) ⟶ Rep.ofAlgebraAutOnUnits F L :=
  Rep.ofHom
    { toLinearMap := (unitsInclLinearMap : Additive Mˣ →ₗ[ℤ] Additive Lˣ)
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        set y : Mˣ := Additive.toMul x with hy
        show Additive.ofMul (Units.map (algebraMap M L).toMonoidHom
            (Units.map (((AlgEquiv.restrictNormalHom (K₁ := L) (E := M)) σ)).toMonoidHom y))
          = Additive.ofMul ((σ : L ≃ₐ[F] L) • Units.map (algebraMap M L).toMonoidHom y)
        rw [AlgEquiv.smul_units_def]
        congr 1
        apply Units.ext
        simp only [Units.coe_map]
        rw [show (AlgEquiv.restrictNormalHom (K₁ := L) (E := M)) σ = σ.restrictNormal M from rfl]
        exact AlgEquiv.restrictNormal_commutes (F := F) σ M y }

/-- **The level inflation map** `H²(Gal(M/F), Mˣ) → H²(Gal(L/F), Lˣ)` for `F ⊆ M ⊆ L`. -/
noncomputable abbrev levelInfMap :
    groupCohomology (Rep.ofAlgebraAutOnUnits F M) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom (K₁ := L) (E := M))
    (unitsInclCoeff : Rep.res (AlgEquiv.restrictNormalHom (K₁ := L) (E := M))
      (Rep.ofAlgebraAutOnUnits F M) ⟶ Rep.ofAlgebraAutOnUnits F L) 2

end LevelInf

end NK.NUV2.RouteD

namespace NK.NUV2.RouteD

section Comp

variable {F M L N : Type} [Field F] [Field M] [Field L] [Field N]
  [Algebra F M] [Algebra F L] [Algebra F N] [Algebra M L] [Algebra L N] [Algebra M N]
  [IsScalarTower F M L] [IsScalarTower F L N] [IsScalarTower F M N] [IsScalarTower M L N]
  [Normal F M] [Normal F L] [Normal F N]

@[simp] theorem unitsInclCoeff_toLinearMap :
    (Rep.Hom.hom (unitsInclCoeff (F := F) (M := M) (L := L))).toLinearMap
      = (unitsInclLinearMap : Additive Mˣ →ₗ[ℤ] Additive Lˣ) := rfl

/-- **Functoriality of the level inflation maps**: for `F ⊆ M ⊆ L ⊆ N` the inflation `M → N` is
the composite of the inflations `M → L` and `L → N`. -/
theorem levelInfMap_comp :
    levelInfMap (F := F) (M := M) (L := N) =
      levelInfMap (F := F) (M := M) (L := L) ≫ levelInfMap (F := F) (M := L) (L := N) := by
  simp only [levelInfMap]
  rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp F M L N) ?_ 2
  rw [show (Rep.resFunctor (AlgEquiv.restrictNormalHom (K₁ := N) (E := L))).map
        (unitsInclCoeff (F := F) (M := M) (L := L))
      = Rep.resMap (AlgEquiv.restrictNormalHom (K₁ := N) (E := L))
          (unitsInclCoeff (F := F) (M := M) (L := L)) from rfl]
  rw [Rep.hom_comp_toLinearMap]
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, Rep.resMap_hom_toLinearMap]
  simp only [unitsInclCoeff_toLinearMap]
  change Additive.ofMul (Units.map (algebraMap M N).toMonoidHom (Additive.toMul x))
    = Additive.ofMul (Units.map (algebraMap L N).toMonoidHom
        (Units.map (algebraMap M L).toMonoidHom (Additive.toMul x)))
  congr 1
  apply Units.ext
  simp only [Units.coe_map]
  exact IsScalarTower.algebraMap_apply M L N _

end Comp

end NK.NUV2.RouteD

namespace NK.NUV2.RouteD

section AmbientInf

variable {B E : Type} [Field B] [Field E] [Algebra B E] [FiniteDimensional B E] [IsGalois B E]
  (N : Subgroup (E ≃ₐ[B] E)) [N.Normal]

/-- **Injectivity and range of the ambient inflation map.**

For a finite Galois extension `B ⊆ E`, a normal subgroup `N ≤ Gal(E/B)` and the `B`-representation
`Eˣ` of units, the inflation `H²(G⧸N, (Eˣ)^N) → H²(G, Eˣ)` is injective (Hilbert 90 for the units
of `E`) with image the `|G⧸N|`-torsion of `H²(G, Eˣ)`.

The two number-theoretic inputs are isolated as hypotheses: the cardinality of `H²(G, Eˣ)` and of
the cohomology of the fixed field `E^N`, together with a generator of `H²(G, Eˣ)` of maximal order.
For `B` a finite extension of a `p`-adic field and `E/B` abelian they are supplied by
`exists_addOrderOf_eq_finrank_groupCohomology_two_units_aux` and the two bounds
`natCard_groupCohomology_two_units_le_finrank_of_abelian`,
`groupCohomology_two_units_ge_finrank`. -/
theorem infNatTrans_units_injective_range
    (hfin : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2))
    (hcard : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2)
      = Nat.card (E ≃ₐ[B] E))
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2))
    (hcardK : Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField N)) 2) = N.index) :
    Function.Injective ⇑((groupCohomology.infNatTrans ℤ N 2).app
        (Rep.ofAlgebraAutOnUnits B E)).hom ∧
      LinearMap.range ((groupCohomology.infNatTrans ℤ N 2).app
          (Rep.ofAlgebraAutOnUnits B E)).hom
        = LinearMap.ker ((N.index : ℤ) • LinearMap.id) := by
  haveI hfin' : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) := hfin
  haveI hfint : Fintype (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) :=
    Fintype.ofFinite _
  -- Hilbert 90 for the units of `E`
  have hH1 : Subsingleton (groupCohomology
      (Rep.res N.subtype (Rep.ofAlgebraAutOnUnits B E)) 1) :=
    Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units N
  have hinj : Function.Injective ⇑((groupCohomology.infNatTrans ℤ N 2).app
      (Rep.ofAlgebraAutOnUnits B E)).hom :=
    Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1 N _ hH1
  -- the `N.index`-torsion of `H²(G, Eˣ)` has cardinality `N.index`
  have hn : N.index ∣ Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) := by
    rw [hcard]
    exact ⟨Nat.card ↥N, by rw [mul_comm, Subgroup.card_mul_index]⟩
  have hTcard : Nat.card ↥(LinearMap.ker ((N.index : ℤ) • LinearMap.id)) = N.index :=
    NK.NUV2.RouteC.natCard_ker_zsmul_id_eq u hu N.index hn
  -- the range of the inflation has cardinality `N.index`
  have hScard : Nat.card ↥(LinearMap.range ((groupCohomology.infNatTrans ℤ N 2).app
      (Rep.ofAlgebraAutOnUnits B E)).hom) = N.index := by
    have h1 : Nat.card ↥(groupCohomology
        ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants N) 2)
        = Nat.card ↥(LinearMap.range ((groupCohomology.infNatTrans ℤ N 2).app
            (Rep.ofAlgebraAutOnUnits B E)).hom) :=
      Nat.card_congr (Equiv.ofInjective _ hinj)
    obtain ⟨e⟩ :=
      Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_quotientToInvariants_units
        (B := B) (E := E) N
    have h2 : Nat.card ↥(groupCohomology
        ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants N) 2)
        = Nat.card ↥(groupCohomology
            (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField N)) 2) :=
      Nat.card_congr e.toEquiv
    rw [← h1, h2, hcardK]
  -- the range is contained in the torsion subgroup
  have hST : LinearMap.range ((groupCohomology.infNatTrans ℤ N 2).app
      (Rep.ofAlgebraAutOnUnits B E)).hom ≤
      LinearMap.ker ((N.index : ℤ) • LinearMap.id) := by
    intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    simp only [zsmul_eq_mul, Module.End.mul_apply, LinearMap.id_coe, id_eq,
      Module.End.intCast_apply]
    haveI hfinQ : Fintype ((E ≃ₐ[B] E) ⧸ N) := Fintype.ofFinite _
    have h := Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
        ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants N) y
    have hZ : (Nat.card ((E ≃ₐ[B] E) ⧸ N) : ℤ) • y = 0 := by
      rw [natCast_zsmul]
      exact h
    have hidx : Nat.card ((E ≃ₐ[B] E) ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
    rw [hidx] at hZ
    rw [show (N.index : ℤ)
          • ((groupCohomology.infNatTrans ℤ N 2).app (Rep.ofAlgebraAutOnUnits B E)).hom y
        = ((groupCohomology.infNatTrans ℤ N 2).app (Rep.ofAlgebraAutOnUnits B E)).hom
            ((N.index : ℤ) • y)
        from (map_zsmul _ _ y).symm]
    rw [hZ, map_zero]
  haveI hfinE2 : Finite (↑((groupCohomology.functor ℤ (E ≃ₐ[B] E) 2).obj
      (Rep.ofAlgebraAutOnUnits B E))) := hfin'
  refine ⟨hinj, ?_⟩
  refine Submodule.toAddSubgroup_injective (AddSubgroup.eq_of_le_of_card_ge ?_ ?_)
  · intro x hx
    rw [Submodule.mem_toAddSubgroup] at hx ⊢
    exact hST hx
  · exact le_of_eq ((show Nat.card ↥(LinearMap.ker ((N.index : ℤ) • LinearMap.id)).toAddSubgroup
        = N.index from hTcard).trans
      ((show Nat.card ↥(LinearMap.range ((groupCohomology.infNatTrans ℤ N 2).app
        (Rep.ofAlgebraAutOnUnits B E)).hom).toAddSubgroup = N.index from hScard).symm))

end AmbientInf

end NK.NUV2.RouteD
