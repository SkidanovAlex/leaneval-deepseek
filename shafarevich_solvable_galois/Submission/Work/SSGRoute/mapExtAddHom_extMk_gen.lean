import Mathlib
import Submission.Work.SSGRoute.MapExtAuxDefs
import Submission.Work.SSGRoute.phiSharp_f
import Submission.Work.SSGRoute.MapUniv.derived_left
import Submission.Work.SSGRoute.phiSharp_cocycleB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SSGRoute.mapExtAddHom_extMk_gen`

The "L–M" lemma: `Ext`-computation commutes with an exact additive functor along a lift of the
projective resolution.  The proof is the derived-category computation of `E0bMapExt.lean`: after
`ext` and the normalisations of `Abelian.Ext`, both sides are rewritten using

* `MapUniv.derived_left` (the augmentation compatibility of `phiSharp`, transported to the derived
  category),
* the normal form `extMk_hom` of `ProjectiveResolution.extMk`,
* `phiSharp_f` and `phiSharp_cocycleB` (the comparison of the cocycles),
* `phiSharp_augmentation` (via `MapUniv`).

The two "auxiliary inputs" of `LM_HINTS.md` are proved inline (`hα`, `hβ` for the normal form of
`extMk.hom`).
-/

open CategoryTheory Limits

namespace Work.SSGRoute

universe u v u' v'

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 16000000 in

theorem mapExtAddHom_extMk_gen {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} (R : ProjectiveResolution X) {n : ℕ} (g : R.complex.X n ⟶ Y)
    (hg : R.complex.d (n + 1) n ≫ g = 0)
    {X' : D} (R' : ProjectiveResolution X') (g' : X' ⟶ F.obj X)
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
    (hφ : φ ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map R.π ≫
        (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X
        = R'.π ≫ (ChainComplex.single₀ D).map g')
    (hg' : R'.complex.d (n + 1) n ≫ (φ.f n ≫ F.map g) = 0) :
    (Abelian.Ext.mk₀ g').comp ((R.extMk g (n + 1) rfl hg).mapExactFunctor F) (zero_add n)
      = R'.extMk (φ.f n ≫ F.map g) (n + 1) rfl hg' := by

  haveI := HasDerivedCategory.standard C
  haveI := HasDerivedCategory.standard D
  have hf₀c : R.cochainComplex.d (-(↑n + 1)) (-(↑n : ℤ)) ≫
      ((R.cochainComplexXIso (-(↑n : ℤ)) n rfl).hom ≫ g) = 0 := by
    simpa [R.cochainComplex_d (-(↑n+1)) (-↑n) (n+1) n (by simp) rfl, hg]
  have hf₀c' : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex).d (-(↑n + 1)) (-(↑n : ℤ)) ≫
      F.map ((R.cochainComplexXIso (-(↑n : ℤ)) n rfl).hom ≫ g) = 0 := by
    change F.map (R.cochainComplex.d (-(↑n + 1)) (-(↑n : ℤ))) ≫
      F.map ((R.cochainComplexXIso (-(↑n : ℤ)) n rfl).hom ≫ g) = 0
    rw [← F.map_comp, hf₀c, F.map_zero]
  have hα : (R.extMk g (n + 1) rfl hg).hom
      = (inv (DerivedCategory.Q.map R.π') ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) DerivedCategory.Q :
            ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X)
              ((DerivedCategory.singleFunctor C 0).obj Y) (n : ℤ)) := by
    rw [ProjectiveResolution.extMk_hom]
    have hA : (ShiftedHom.mk₀ (0:ℤ) rfl
          ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫ inv (DerivedCategory.Q.map R.π')))
        = ShiftedHom.mk₀ (0:ℤ) rfl (inv (DerivedCategory.Q.map R.π') :
            (DerivedCategory.singleFunctor C 0).obj X ⟶ DerivedCategory.Q.obj R.cochainComplex) :=
      congrArg (fun (ψ : (DerivedCategory.singleFunctor C 0).obj X ⟶
          DerivedCategory.Q.obj R.cochainComplex) => ShiftedHom.mk₀ (0:ℤ) rfl ψ)
        (Category.id_comp (inv (DerivedCategory.Q.map R.π')))
    have hC : (ShiftedHom.mk₀ (0:ℤ) rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
        = ShiftedHom.mk₀ (0:ℤ) rfl
            (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y))) :=
      congrArg (fun (ψ : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y) ⟶
          DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y)) =>
            ShiftedHom.mk₀ (0:ℤ) rfl ψ)
        (show ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y :
              DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y) ⟶
                DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y)) = 𝟙 _ from rfl)
    rw [hA, hC]
    rw [ShiftedHom.comp_mk₀_id]
    rw [ShiftedHom.mk₀_comp]
    simp only [Work.SSGRoute.extMkShiftedHom]
  have hβ : (R'.extMk (φ.f n ≫ F.map g) (n + 1) rfl hg').hom
      = (inv (DerivedCategory.Q.map R'.π') ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R' (φ.f n ≫ F.map g) hg') DerivedCategory.Q :
            ShiftedHom ((DerivedCategory.singleFunctor D 0).obj X')
              ((DerivedCategory.singleFunctor D 0).obj (F.obj Y)) (n : ℤ)) := by
    rw [ProjectiveResolution.extMk_hom]
    have hA : (ShiftedHom.mk₀ (0:ℤ) rfl
          ((DerivedCategory.singleFunctorIsoCompQ D 0).hom.app X' ≫ inv (DerivedCategory.Q.map R'.π')))
        = ShiftedHom.mk₀ (0:ℤ) rfl (inv (DerivedCategory.Q.map R'.π') :
            (DerivedCategory.singleFunctor D 0).obj X' ⟶ DerivedCategory.Q.obj R'.cochainComplex) :=
      congrArg (fun (ψ : (DerivedCategory.singleFunctor D 0).obj X' ⟶
          DerivedCategory.Q.obj R'.cochainComplex) => ShiftedHom.mk₀ (0:ℤ) rfl ψ)
        (Category.id_comp (inv (DerivedCategory.Q.map R'.π')))
    have hC : (ShiftedHom.mk₀ (0:ℤ) rfl ((DerivedCategory.singleFunctorIsoCompQ D 0).inv.app (F.obj Y)))
        = ShiftedHom.mk₀ (0:ℤ) rfl
            (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor D 0).obj (F.obj Y)))) :=
      congrArg (fun (ψ : DerivedCategory.Q.obj ((CochainComplex.singleFunctor D 0).obj (F.obj Y)) ⟶
          DerivedCategory.Q.obj ((CochainComplex.singleFunctor D 0).obj (F.obj Y))) =>
            ShiftedHom.mk₀ (0:ℤ) rfl ψ)
        (show ((DerivedCategory.singleFunctorIsoCompQ D 0).inv.app (F.obj Y) :
              DerivedCategory.Q.obj ((CochainComplex.singleFunctor D 0).obj (F.obj Y)) ⟶
                DerivedCategory.Q.obj ((CochainComplex.singleFunctor D 0).obj (F.obj Y))) = 𝟙 _ from rfl)
    rw [hA, hC]
    rw [ShiftedHom.comp_mk₀_id]
    rw [ShiftedHom.mk₀_comp]
    simp only [Work.SSGRoute.extMkShiftedHom]
  -- hd, from MapUniv.derived_left
  have hd : (DerivedCategory.singleFunctor D 0).map g' ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X
      = inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ)
          ≫ (F.mapDerivedCategoryFactors).inv.app R.cochainComplex
          ≫ F.mapDerivedCategory.map (DerivedCategory.Q.map R.π') := by
    have h := MapUniv.derived_left F R R' g' φ hφ
    rwa [show MapUniv.phiSharp F R R' φ = Work.SSGRoute.phiSharp F R R' φ from rfl] at h
  have h3 : (DerivedCategory.singleFunctor D 0).map g' ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π'))
      = inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ) ≫
        F.mapDerivedCategoryFactors.inv.app R.cochainComplex := by
    rw [← Category.assoc ((DerivedCategory.singleFunctor D 0).map g')
          ((F.mapDerivedCategorySingleFunctor 0).inv.app X)
          (F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π')))]
    rw [hd, Functor.map_inv]
    simp only [Category.assoc]
    rw [IsIso.hom_inv_id, Category.comp_id]
  -- h2
  have h2 : (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π'))
      = DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app X) ≫
        inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')) ≫
        F.mapDerivedCategoryFactors.inv.app R.cochainComplex := by
    have hA : (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X)
        = DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app X) :=
      Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app F X
    have hnat : DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π') ≫
        F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X)
        = F.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
          F.mapDerivedCategory.map (DerivedCategory.Q.map R.π') := by
      have h := (F.mapDerivedCategoryFactors.inv).naturality R.π'
      simpa only [Functor.comp_map] using h
    have hnat2 : F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) ≫
          inv (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π'))
        = inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')) ≫
          F.mapDerivedCategoryFactors.inv.app R.cochainComplex := by
      have e1 : inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')) ≫
          (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π') ≫
            (F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) ≫
              inv (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π'))))
          = F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) ≫
            inv (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π')) :=
        IsIso.inv_hom_id_assoc _ _
      have e2 : inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')) ≫
          (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π') ≫
            (F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) ≫
              inv (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π'))))
          = inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')) ≫
            F.mapDerivedCategoryFactors.inv.app R.cochainComplex := by
        rw [← Category.assoc (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π'))
              (F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X))
              (inv (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π'))),
          hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [← e1, e2]
    have hins : (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
          F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π'))
        = (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
          F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
          F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) ≫
          F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π')) := by
      rw [← Category.assoc (F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X))
        (F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X)),
        Iso.hom_inv_id_app, Category.id_comp]
    rw [hins, ← Category.assoc, hA]
    rw [show F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) ≫
        F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π'))
        = F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) ≫
          inv (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π')) from by rw [Functor.map_inv]]
    rw [hnat2]
  -- hν
  have hν : ShiftedHom.map (inv (DerivedCategory.Q.map R.π') ≫
        ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) DerivedCategory.Q) F.mapDerivedCategory
      = F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π')) ≫
        ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
          (DerivedCategory.Q ⋙ F.mapDerivedCategory) := by
    rw [show inv (DerivedCategory.Q.map R.π') ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) DerivedCategory.Q
        = (ShiftedHom.mk₀ 0 rfl (inv (DerivedCategory.Q.map R.π'))).comp
            (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) DerivedCategory.Q) (add_zero (n : ℤ))
        from (ShiftedHom.mk₀_comp 0 rfl _ _).symm]
    rw [ShiftedHom.map_comp, ShiftedHom.map_mk₀, ← ShiftedHom.comp_map, ShiftedHom.mk₀_comp]
  -- hB
  have hB : (F.mapDerivedCategorySingleFunctor 0).hom.app Y
      = F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj Y) ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y) := by
    have h := Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app F Y
    rw [show DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app Y)
        = DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)
        from rfl] at h
    rw [← h, ← Category.assoc]
    erw [Iso.hom_inv_id_app]
    rw [Category.id_comp]
  -- hν2
  have hν2 : ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
          (DerivedCategory.Q ⋙ F.mapDerivedCategory) ≫
        (F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj Y))⟦(n : ℤ)⟧'
      = F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫
        ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) := by
    have h := ShiftedHom.map_naturality (Work.SSGRoute.extMkShiftedHom R g hg)
      F.mapDerivedCategoryFactors.hom
    rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
    exact h
  -- hQ
  have hQ : ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
      = ShiftedHom.map (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
          (F.mapHomologicalComplex (ComplexShape.up ℤ))) DerivedCategory.Q :=
    ShiftedHom.comp_map _ _ _
  -- hQ2
  have hQ2 : ShiftedHom.map (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
        (F.mapHomologicalComplex (ComplexShape.up ℤ))) DerivedCategory.Q ≫
        (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))⟦(n : ℤ)⟧'
      = ShiftedHom.map (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
          (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≫
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)⟦(n : ℤ)⟧') DerivedCategory.Q := by
    rw [ShiftedHom.map, ShiftedHom.map, Category.assoc]
    erw [← Functor.commShiftIso_hom_naturality DerivedCategory.Q
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y) (n : ℤ)]
    rw [← Category.assoc, ← Functor.map_comp]
    rfl
  -- hk
  have hk : Work.SSGRoute.phiSharp F R R' φ ≫
        (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
            (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≫
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)⟦(n : ℤ)⟧')
      = Work.SSGRoute.extMkShiftedHom R' (φ.f n ≫ F.map g) hg' :=
    phiSharp_cocycleB F R g hg R' φ hg'
  -- ASSEMBLY
  ext
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mapExactFunctor_hom, Abelian.Ext.mk₀_hom, hα, hβ]
  rw [ShiftedHom.mk₀_comp]
  calc (DerivedCategory.singleFunctor D 0).map g' ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        ShiftedHom.map (inv (DerivedCategory.Q.map R.π') ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) DerivedCategory.Q) F.mapDerivedCategory ≫
        (shiftFunctor (DerivedCategory D) (n : ℤ)).map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)
      = (DerivedCategory.singleFunctor D 0).map g' ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
          (F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π')) ≫
            ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) (DerivedCategory.Q ⋙ F.mapDerivedCategory)) ≫
          (shiftFunctor (DerivedCategory D) (n : ℤ)).map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) := by rw [hν]
    _ = ((DerivedCategory.singleFunctor D 0).map g' ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
            F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π'))) ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) (DerivedCategory.Q ⋙ F.mapDerivedCategory) ≫
          (shiftFunctor (DerivedCategory D) (n : ℤ)).map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) := by
          simp only [Category.assoc]
    _ = (inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ) ≫
            F.mapDerivedCategoryFactors.inv.app R.cochainComplex) ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) (DerivedCategory.Q ⋙ F.mapDerivedCategory) ≫
          (shiftFunctor (DerivedCategory D) (n : ℤ)).map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) := by
          rw [h3]
    _ = inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ) ≫
          F.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) (DerivedCategory.Q ⋙ F.mapDerivedCategory) ≫
          (shiftFunctor (DerivedCategory D) (n : ℤ)).map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) := by
          simp only [Category.assoc]
    _ = inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ) ≫
          F.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg) (DerivedCategory.Q ⋙ F.mapDerivedCategory) ≫
          (F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj Y))⟦(n : ℤ)⟧' ≫
          (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))⟦(n : ℤ)⟧' := by
          rw [hB, Functor.map_comp]
    _ = inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ) ≫
          (F.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
            F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫
            ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)) ≫
          (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))⟦(n : ℤ)⟧' := by
          rw [← Category.assoc (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
                (DerivedCategory.Q ⋙ F.mapDerivedCategory))
              ((F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj Y))⟦(n : ℤ)⟧')
              ((DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))⟦(n : ℤ)⟧')]
          rw [hν2]
          simp only [Category.assoc]
    _ = inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ) ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) ≫
          (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))⟦(n : ℤ)⟧' := by
          rw [show F.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
              F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫
              ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
              = ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) from
            (by rw [Iso.inv_hom_id_app_assoc])]
    _ = inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ) ≫
          ShiftedHom.map (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
            (F.mapHomologicalComplex (ComplexShape.up ℤ))) DerivedCategory.Q ≫
          (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))⟦(n : ℤ)⟧' := by
          rw [hQ]
    _ = inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ) ≫
          ShiftedHom.map (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
            (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≫
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)⟦(n : ℤ)⟧') DerivedCategory.Q := by
          rw [hQ2]
    _ = inv (DerivedCategory.Q.map R'.π') ≫ ShiftedHom.map
          (Work.SSGRoute.phiSharp F R R' φ ≫
            (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
              (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≫
              ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)⟦(n : ℤ)⟧'))
          DerivedCategory.Q := by
          rw [show ShiftedHom.map (Work.SSGRoute.phiSharp F R R' φ ≫
                (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
                  (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≫
                  ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)⟦(n : ℤ)⟧'))
                DerivedCategory.Q
              = DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ) ≫
                ShiftedHom.map (ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
                  (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≫
                  ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)⟦(n : ℤ)⟧')
                  DerivedCategory.Q from by
            rw [ShiftedHom.map, ShiftedHom.map, Functor.map_comp, Category.assoc]
            rfl]
    _ = inv (DerivedCategory.Q.map R'.π') ≫
          ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R' (φ.f n ≫ F.map g) hg') DerivedCategory.Q := by
          rw [hk]

end Work.SSGRoute
