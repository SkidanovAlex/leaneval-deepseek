import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.classIncl_isCanonical
import Submission.Work.SSGRoute.phiAt_level_infl
import Submission.Work.SSGRoute.PT.extLoc_yonedaPair
import Submission.Work.SSGRoute.PT.pt_pairing_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-! ## Universe-pinned versions of the idèle and class-group representations

`NK.GlobalCFT.Idele` and `NK.GlobalCFT.IdeleClassGroup` are declared at an implicit universe, so
`idelesK k K` and `classesK k K` carry a universe metavariable which the `Rep`-level lemmas of
`PTDefs` leave free.  The abbreviations below pin the carrier universe to `0` (`Coeff = ULift ℤ`),
which is what the `Ext` core of `PTDefs` uses; all statements below are phrased with them.
-/

/-- `𝕀_K` with the carrier universe pinned. -/
abbrev idelesRepP (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] :
    Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K) := NK.HassePrinciple.ideleRep k K

/-- `C_K` with the carrier universe pinned. -/
abbrev classesRepP (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K) := NK.HassePrinciple.classGroupRep k K

/-- The class-group map with pinned universes. -/
theorem classGroupMap_applyP (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] (x : Idele K) :
    (Rep.Hom.hom (NK.HassePrinciple.classGroupMap k K : idelesRepP k K ⟶ classesRepP k K))
        (Additive.ofMul x)
      = (Additive.ofMul (IdeleClassGroup.mk K x) : classesRepP k K) :=
  NK.HassePrinciple.classGroupMap_apply k K x

/-- The canonical idèle-level data underlying `classIncl k K L`. -/
structure CanonicalIdleData (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L] where
  u : Place L → Place K
  hu : ∀ w : Place L, Place.LiesOver w (u w)
  φ : Idele K →* Idele L
  hφ : ∀ (x : Idele K) (w : Place L),
    φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))
  hι : ∀ x : Idele K,
    (classIncl k K L).hom (Additive.ofMul (IdeleClassGroup.mk K x) : classesRepP k K)
      = (Additive.ofMul (IdeleClassGroup.mk L (φ x)) : classesRepP k L)

/-- A choice of the canonical idèle-level data. -/
def canonicalIdleData (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L] :
    CanonicalIdleData k K L := by
  classical
  have h := classIncl_isCanonical k K L
  have h1 := Classical.choose_spec h
  have h3 := Classical.choose_spec h1
  have h5 := Classical.choose_spec h3
  exact ⟨Classical.choose h, Classical.choose h1, Classical.choose h3, h5.1, h5.2⟩

/-- The compatibility of the chosen idèle map with `classIncl`. -/
theorem classIncl_hιP (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (x : Idele K) :
    (classIncl k K L).hom (Additive.ofMul (IdeleClassGroup.mk K x) : classesRepP k K)
      = (Additive.ofMul (IdeleClassGroup.mk L ((canonicalIdleData k K L).φ x)) :
          classesRepP k L) :=
  (canonicalIdleData k K L).hι x

/-- **The idèle map `𝕀_K →* 𝕀_L` as a morphism of `Gal(L/k)`-modules.** -/
def idleRepMap (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L] :
    Rep.res (galRes k K L) (idelesRepP k K) ⟶ idelesRepP k L :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul ((canonicalIdleData k K L).φ (Additive.toMul x))
      map_add' := fun a b => by
        show Additive.ofMul ((canonicalIdleData k K L).φ (Additive.toMul (a + b)))
          = Additive.ofMul ((canonicalIdleData k K L).φ (Additive.toMul a))
            + Additive.ofMul ((canonicalIdleData k K L).φ (Additive.toMul b))
        rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        show Additive.ofMul ((canonicalIdleData k K L).φ (Additive.toMul (z • x)))
          = z • Additive.ofMul ((canonicalIdleData k K L).φ (Additive.toMul x))
        rw [toMul_zsmul, map_zpow, ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro y
        exact congrArg Additive.ofMul
          ((NK.HassePrinciple.ideleInclusion_smul_restrict (K := k) (F := K) (L := L)
            (canonicalIdleData k K L).u (canonicalIdleData k K L).hu
            (canonicalIdleData k K L).φ (canonicalIdleData k K L).hφ σ
            (Additive.toMul y)).symm) }

/-- The underlying function of `idleRepMap` is the idèle map `φ`. -/
@[simp]
private theorem idleRepMap_apply (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (x : Additive (Idele K)) :
    (idleRepMap k K L).hom x
      = (Additive.ofMul ((canonicalIdleData k K L).φ (Additive.toMul x)) :
          idelesRepP k L) := rfl

/-- **The idèle level map commutes with the maps to the class groups.** -/
theorem resMap_classGroupMap_comp_classIncl (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L] :
    Rep.resMap (galRes k K L)
        (NK.HassePrinciple.classGroupMap k K : idelesRepP k K ⟶ classesRepP k K) ≫
      classIncl k K L
      = idleRepMap k K L ≫
          (NK.HassePrinciple.classGroupMap k L : idelesRepP k L ⟶ classesRepP k L) := by
  apply Rep.hom_ext
  ext y
  change (Rep.Hom.hom ((Rep.resMap (galRes k K L)
      (NK.HassePrinciple.classGroupMap k K : idelesRepP k K ⟶ classesRepP k K)) ≫
      classIncl k K L)) y
    = (Rep.Hom.hom (idleRepMap k K L ≫
        (NK.HassePrinciple.classGroupMap k L : idelesRepP k L ⟶ classesRepP k L))) y
  rw [Rep.comp_apply, Rep.comp_apply, Rep.resMap_hom_apply]
  obtain ⟨z, hz⟩ : ∃ z : Idele K, y = Additive.ofMul z := ⟨Additive.toMul y, rfl⟩
  rw [hz]
  change (Rep.Hom.hom (classIncl k K L))
      ((Rep.Hom.hom (NK.HassePrinciple.classGroupMap k K : idelesRepP k K ⟶ classesRepP k K))
        (Additive.ofMul z))
    = (Rep.Hom.hom (NK.HassePrinciple.classGroupMap k L : idelesRepP k L ⟶ classesRepP k L))
      ((Rep.Hom.hom (idleRepMap k K L)) (Additive.ofMul z))
  calc (classIncl k K L).hom
        ((NK.HassePrinciple.classGroupMap k K : idelesRepP k K ⟶ classesRepP k K).hom
          (Additive.ofMul z))
      = (classIncl k K L).hom (Additive.ofMul (IdeleClassGroup.mk K z) : classesRepP k K) :=
        congrArg (fun w => (classIncl k K L).hom w) (classGroupMap_applyP k K z)
    _ = (Additive.ofMul (IdeleClassGroup.mk L ((canonicalIdleData k K L).φ z)) :
          classesRepP k L) := classIncl_hιP k K L z
    _ = (NK.HassePrinciple.classGroupMap k L : idelesRepP k L ⟶ classesRepP k L).hom
          (Additive.ofMul ((canonicalIdleData k K L).φ z)) :=
        (classGroupMap_applyP k L ((canonicalIdleData k K L).φ z)).symm
    _ = (NK.HassePrinciple.classGroupMap k L : idelesRepP k L ⟶ classesRepP k L).hom
          ((idleRepMap k K L).hom (Additive.ofMul z)) :=
        congrArg (fun w =>
          (NK.HassePrinciple.classGroupMap k L : idelesRepP k L ⟶ classesRepP k L).hom w)
          (idleRepMap_apply k K L (Additive.ofMul z)).symm

/-! ## `Ext`-calculus lemmas for `levelPair` -/

/-- **`levelPair` is compatible with precomposing the `Ext`-class with a degree-`0` coefficient
map.** -/
theorem levelPair_comp_mk₀ {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A A' : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H}
    (ι : Rep.res f A ⟶ B) (β : A' ⟶ A)
    {r s : ℕ} (x : Abelian.Ext M A' r) (h : extH (Rep.res f M) s) :
    levelPair f ι (x.comp (Abelian.Ext.mk₀ β) (add_zero r)) h
      = levelPair f (Rep.resMap f β ≫ ι) x h := by
  have hx : extRes f (x.comp (Abelian.Ext.mk₀ β) (add_zero r))
      = (extRes f x).comp (Abelian.Ext.mk₀ (Rep.resMap f β)) (add_zero r) := by
    rw [extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
    rfl
  rw [levelPair, levelPair, hx,
    Abelian.Ext.comp_assoc_of_second_deg_zero (extRes f x)
      (Abelian.Ext.mk₀ (Rep.resMap f β)) (Abelian.Ext.mk₀ ι) (add_zero r),
    Abelian.Ext.mk₀_comp_mk₀]

/-- **`levelPair` is compatible with postcomposing the coefficient map.** -/
theorem levelPair_comp_ι {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0, 0, 0} Coeff G} {B B' : Rep.{0, 0, 0} Coeff H}
    (ι₁ : Rep.res f A ⟶ B) (ι₂ : B ⟶ B')
    {r s : ℕ} (x : Abelian.Ext M A r) (h : extH (Rep.res f M) s) :
    levelPair f (ι₁ ≫ ι₂) x h
      = (levelPair f ι₁ x h).comp (Abelian.Ext.mk₀ ι₂) (add_zero (s + r)) := by
  rw [levelPair, levelPair,
    Abelian.Ext.comp_assoc_of_third_deg_zero h
      ((extRes f x).comp (Abelian.Ext.mk₀ ι₁) (add_zero r)) (Abelian.Ext.mk₀ ι₂) rfl,
    ← Abelian.Ext.mk₀_comp_mk₀ ι₁ ι₂,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero (extRes f x)
      (Abelian.Ext.mk₀ ι₁) (Abelian.Ext.mk₀ ι₂) (add_zero r)]

/-- **The idèle lifting identity.** -/
theorem phiAt_extToClasses_eq_idleRepMap (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L]
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))
    (z : Abelian.Ext M (idelesRepP k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) :
    phiAt (k := k) (K := K) (L := L) (extToClasses z) h
      = (levelPair (galRes k K L) (idleRepMap k K L) z h).comp
          (Abelian.Ext.mk₀
            (NK.HassePrinciple.classGroupMap k L : idelesRepP k L ⟶ classesRepP k L))
          (add_zero 2) := by
  rw [phiAt, extToClasses]
  rw [levelPair_comp_mk₀ (galRes k K L) (classIncl k K L)
    (NK.HassePrinciple.classGroupMap k K : idelesRepP k K ⟶ classesRepP k K) z h]
  rw [resMap_classGroupMap_comp_classIncl k K L]
  rw [levelPair_comp_ι]

/-- **`levelPair` in Yoneda form.** -/
theorem levelPair_eq_yonedaPair {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x : Abelian.Ext M A r) (h : extH (Rep.res f M) s) :
    levelPair f ι x h
      = yonedaPair ((extRes f x).comp (Abelian.Ext.mk₀ ι) (add_zero r)) h := rfl

/-- **Localisation of the idèle-valued pairing class.** -/
theorem extLoc_levelPair_idleRepMap_eq (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L]
    (M : Rep Coeff (K ≃ₐ[k] K))
    (z : Abelian.Ext M (idelesRepP k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) (w : Place L) :
    extLoc (k := k) (K := L) w (levelPair (galRes k K L) (idleRepMap k K L) z h)
      = yonedaPair
          (extLoc (k := k) (K := L) w ((extRes (galRes k K L) z).comp
            (Abelian.Ext.mk₀ (idleRepMap k K L)) (add_zero 1)))
          (extHRestrict (decompK (k := k) (K := L) w) h) := by
  rw [levelPair_eq_yonedaPair]
  exact PT.extLoc_yonedaPair (k := k) (K := L) _ h w

end Work.SSGRoute
