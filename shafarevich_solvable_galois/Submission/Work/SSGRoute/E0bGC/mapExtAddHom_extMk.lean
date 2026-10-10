import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E0bGC.toSingleMk_map
import Submission.Work.SSGRoute.MapUniv.phiSharp_augmentation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E0bGC

open CategoryTheory
universe u v w u' v' w'

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mapExtAddHom_extMk {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D]
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
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  have hpa : Work.SSGRoute.phiSharp F R R' φ ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π' ≫
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X
      = R'.π' ≫ (CochainComplex.singleFunctor D 0).map g' := by
    have h := Work.SSGRoute.MapUniv.phiSharp_augmentation F R R' g' φ hφ
    rw [show Work.SSGRoute.MapUniv.phiSharp F R R' φ = Work.SSGRoute.phiSharp F R R' φ from rfl] at h
    exact h
  have hpf := Work.SSGRoute.phiSharp_f F R R' φ n
  have hfC : R.cochainComplex.d (-↑(n+1)) (-↑n) ≫ (R.cochainComplexXIso (-↑n) n rfl).hom ≫ g = 0 := by
    rw [R.cochainComplex_d (-↑(n+1)) (-↑n) (n+1) n (by simp) (by simp)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hg, Limits.comp_zero]
  have hfD : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex).d (-↑(n+1)) (-↑n)
      ≫ F.map ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g) = 0 := by
    rw [Functor.mapHomologicalComplex_obj_d, ← F.map_comp, hfC, F.map_zero]
  have hfE : R'.cochainComplex.d (-↑(n+1)) (-↑n) ≫ (R'.cochainComplexXIso (-↑n) n rfl).hom ≫ φ.f n ≫ F.map g = 0 := by
    rw [R'.cochainComplex_d (-↑(n+1)) (-↑n) (n+1) n (by simp) (by simp)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hg', Limits.comp_zero]

  have hmS : ∀ (B : DerivedCategory C), F.mapDerivedCategory.map (𝟙 B) = 𝟙 (F.mapDerivedCategory.obj B) :=
    fun B => (F.mapDerivedCategory).map_id B
  have hmidC : ∀ (B : DerivedCategory C),
      (shiftFunctor (DerivedCategory C) (n:ℤ)).map (𝟙 B) = 𝟙 (B⟦(n:ℤ)⟧) :=
    fun B => (shiftFunctor (DerivedCategory C) (n:ℤ)).map_id B
  have hmidD : ∀ (B : DerivedCategory D),
      (shiftFunctor (DerivedCategory D) (n:ℤ)).map (𝟙 B) = 𝟙 (B⟦(n:ℤ)⟧) :=
    fun B => (shiftFunctor (DerivedCategory D) (n:ℤ)).map_id B

  have hdelS : ∀ {V : DerivedCategory D}
      (T : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj X) ⟶ V),
      𝟙 (F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj X)) ≫ T = T :=
    fun T => Category.id_comp T
  have hdelS2 : ∀ {V : DerivedCategory D}
      (T : F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj Y)⟦(n:ℤ)⟧) ⟶ V),
      F.mapDerivedCategory.map ((shiftFunctor (DerivedCategory C) (n:ℤ)).map (𝟙 ((DerivedCategory.singleFunctor C 0).obj Y))) ≫ T = T :=
    fun T => by rw [hmidC, hmS, Category.id_comp]
  have hdelT : ∀ {V : DerivedCategory D}
      (T : V ⟶ ((DerivedCategory.singleFunctor D 0).obj (F.obj Y))⟦(n:ℤ)⟧),
      T ≫ (shiftFunctor (DerivedCategory D) (n:ℤ)).map (𝟙 ((DerivedCategory.singleFunctor D 0).obj (F.obj Y))) = T :=
    fun T => by rw [hmidD, Category.comp_id]
  ext
  simp only [Abelian.Ext.comp_hom, Abelian.Ext.mapExactFunctor_hom, ProjectiveResolution.extMk_hom,
    Abelian.Ext.mk₀_hom, DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, ShiftedHom.mk₀_comp, ShiftedHom.map]
  rw [ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀]
  simp only [Functor.map_comp, hmS, hmidC, hmidD, hdelS, hdelS2, hdelT, Category.assoc]
  set W := CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (CochainComplex.HomComplex.Cocycle.toSingleMk ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g)
        (show -↑n + ↑n = 0 by simp) (-↑(n+1)) (by lia) hfC) with hW
  set W2 := CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (CochainComplex.HomComplex.Cocycle.toSingleMk ((R'.cochainComplexXIso (-↑n) n rfl).hom ≫ φ.f n ≫ F.map g)
        (show -↑n + ↑n = 0 by simp) (-↑(n+1)) (by lia) hfE) with hW2
  set W3 := CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (CochainComplex.HomComplex.Cocycle.toSingleMk
        (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex)
        (p := -↑n) (q := 0) (n := (↑n : ℤ))
        (F.map ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g))
        (show -↑n + ↑n = 0 by simp) (-↑(n+1)) (by lia) hfD) with hW3
  have h1 : (DerivedCategory.singleFunctor D 0).map g'
      = 𝟙 ((DerivedCategory.singleFunctor D 0).obj X') ≫ inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ)
        ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')
        ≫ DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X) := by
    have h1'' : DerivedCategory.Q.map R'.π' ≫ DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map g')
        = DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ)
          ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')
          ≫ DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X) := by
      have h := congrArg DerivedCategory.Q.map hpa
      simp only [Functor.map_comp] at h
      simpa only [Category.assoc] using h.symm
    rw [← h1'']
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rfl
  have h3 : DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X)
        ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X
      = F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) := by
    have h : DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X)
          ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X
        = F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) := by
      rw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X]
      simp only [Category.assoc, Iso.hom_inv_id_app]
      erw [Category.comp_id]
      try rfl
    exact h
  have h2 : DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')
        ≫ F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X)
      = F.mapDerivedCategoryFactors.inv.app R.cochainComplex
        ≫ F.mapDerivedCategory.map (DerivedCategory.Q.map R.π') := by
    have h := F.mapDerivedCategoryFactors.inv.naturality R.π'
    simp only [Functor.comp_map] at h
    exact h
  have h4 : F.mapDerivedCategory.map (DerivedCategory.Q.map R.π')
        ≫ F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π')) = 𝟙 _ := by
    rw [← Functor.map_comp, IsIso.hom_inv_id]
    simp
  have h2' : F.mapDerivedCategoryFactors.inv.app R.cochainComplex
        ≫ F.mapDerivedCategory.map (DerivedCategory.Q.map W)
      = DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map W)
        ≫ F.mapDerivedCategoryFactors.inv.app (((CochainComplex.singleFunctor C 0).obj Y)⟦(n:ℤ)⟧) := by
    have h := F.mapDerivedCategoryFactors.inv.naturality W
    simp only [Functor.comp_map] at h
    exact h.symm
  have h5 : F.mapDerivedCategory.map (((DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y))
        ≫ (F.mapDerivedCategory.commShiftIso (n:ℤ)).hom.app ((DerivedCategory.singleFunctor C 0).obj Y)
      = ((DerivedCategory.Q ⋙ F.mapDerivedCategory).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y) := by
    rw [Functor.commShiftIso_comp_hom_app]
    rfl
  have h6 : F.mapDerivedCategoryFactors.inv.app (((CochainComplex.singleFunctor C 0).obj Y)⟦(n:ℤ)⟧)
        ≫ ((DerivedCategory.Q ⋙ F.mapDerivedCategory).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y)
      = (((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y)
        ≫ (F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj Y))⟦(n:ℤ)⟧' := by
    exact ((F.mapDerivedCategoryFactors.inv).shift_app_comm (n:ℤ) ((CochainComplex.singleFunctor C 0).obj Y)).symm
  have h7 : (((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y)
      = DerivedCategory.Q.map (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y))
        ≫ ((DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj Y)) := by
    rw [Functor.commShiftIso_comp_hom_app]
  have h8 : (F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj Y))⟦(n:ℤ)⟧'
        ≫ (shiftFunctor (DerivedCategory D) (n:ℤ)).map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)
      = (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))⟦(n:ℤ)⟧' := by
    rw [← Functor.map_comp]
    congr 1
    exact F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app Y
  have h9 : DerivedCategory.Q.map ((shiftFunctor (CochainComplex D ℤ) (n:ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))
        ≫ ((DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor D 0).obj (F.obj Y))
      = ((DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj Y))
        ≫ (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))⟦(n:ℤ)⟧' := by
    exact ((DerivedCategory.Q).commShiftIso (n:ℤ)).hom.naturality
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)
  have hF3a : W2 = Work.SSGRoute.phiSharp F R R' φ ≫ W3 := by
    simp only [hW2, hW3]
    rw [← CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp]
    congr 1
    rw [← CochainComplex.HomComplex.Cocycle.toSingleMk_precomp]
    apply CochainComplex.HomComplex.Cocycle.ext
    simp only [CochainComplex.HomComplex.Cocycle.toSingleMk_coe]
    have hXY : (R'.cochainComplexXIso (-↑n) n rfl).hom ≫ φ.f n ≫ F.map g
        = (Work.SSGRoute.phiSharp F R R' φ).f (-↑n) ≫ F.map ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g) := by
      calc (R'.cochainComplexXIso (-↑n) n rfl).hom ≫ φ.f n ≫ F.map g
          = ((R'.cochainComplexXIso (-↑n) n rfl).hom ≫ φ.f n) ≫ F.map g := by rw [← Category.assoc]
        _ = ((Work.SSGRoute.phiSharp F R R' φ).f (-↑n) ≫ F.map ((R.cochainComplexXIso (-↑n) n rfl).hom)) ≫ F.map g := by rw [← hpf]
        _ = (Work.SSGRoute.phiSharp F R R' φ).f (-↑n) ≫ (F.map ((R.cochainComplexXIso (-↑n) n rfl).hom) ≫ F.map g) := by rw [Category.assoc]
        _ = (Work.SSGRoute.phiSharp F R R' φ).f (-↑n) ≫ F.map ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g) := by rw [← Functor.map_comp]
    exact congrArg (fun t => CochainComplex.HomComplex.Cochain.toSingleMk t (show -↑n + ↑n = 0 by simp)) hXY
  have hF3b : W3 = ShiftedHom.map W (F.mapHomologicalComplex (ComplexShape.up ℤ))
        ≫ (shiftFunctor (CochainComplex D ℤ) (n:ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y) :=
    toSingleMk_map F ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g)
      (show -↑n + ↑n = 0 by simp) (-↑(n+1)) (by lia) hfC hfD
  have h1r : ∀ {V : DerivedCategory D} (T : _ ⟶ V),
      (DerivedCategory.singleFunctor D 0).map g' ≫ T
        = 𝟙 ((DerivedCategory.singleFunctor D 0).obj X') ≫ inv (DerivedCategory.Q.map R'.π') ≫ DerivedCategory.Q.map (Work.SSGRoute.phiSharp F R R' φ)
          ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')
          ≫ DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X)
          ≫ T := fun T => by rw [h1] <;> simp only [Category.assoc]
  have h3r : ∀ {V : DerivedCategory D} (T : _ ⟶ V),
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X)
        ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ T
        = F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) ≫ T :=
    fun T => by rw [← Category.assoc, h3] <;> simp only [Category.assoc]
  have h2r : ∀ {V : DerivedCategory D} (T : _ ⟶ V),
      DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')
        ≫ F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) ≫ T
        = F.mapDerivedCategoryFactors.inv.app R.cochainComplex
          ≫ F.mapDerivedCategory.map (DerivedCategory.Q.map R.π') ≫ T :=
    fun T => by rw [← Category.assoc, h2] <;> simp only [Category.assoc]
  have h4r : ∀ {V : DerivedCategory D} (T : _ ⟶ V),
      F.mapDerivedCategory.map (DerivedCategory.Q.map R.π')
        ≫ F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π')) ≫ T = T :=
    fun T => by rw [← Category.assoc, h4, Category.id_comp]
  have h2'r : ∀ {V : DerivedCategory D} (T : _ ⟶ V),
      F.mapDerivedCategoryFactors.inv.app R.cochainComplex
        ≫ F.mapDerivedCategory.map (DerivedCategory.Q.map W) ≫ T
        = DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map W)
          ≫ F.mapDerivedCategoryFactors.inv.app (((CochainComplex.singleFunctor C 0).obj Y)⟦(n:ℤ)⟧) ≫ T :=
    fun T => by rw [← Category.assoc, h2'] <;> simp only [Category.assoc]
  have h5r : ∀ {V : DerivedCategory D} (T : _ ⟶ V),
      F.mapDerivedCategory.map (((DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y))
        ≫ (F.mapDerivedCategory.commShiftIso (n:ℤ)).hom.app ((DerivedCategory.singleFunctor C 0).obj Y) ≫ T
        = ((DerivedCategory.Q ⋙ F.mapDerivedCategory).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y) ≫ T :=
    fun T => by rw [← Category.assoc, h5] <;> simp only [Category.assoc]
  have h6r : ∀ {V : DerivedCategory D} (T : _ ⟶ V),
      F.mapDerivedCategoryFactors.inv.app (((CochainComplex.singleFunctor C 0).obj Y)⟦(n:ℤ)⟧)
        ≫ ((DerivedCategory.Q ⋙ F.mapDerivedCategory).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y) ≫ T
        = (((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y)
          ≫ (F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj Y))⟦(n:ℤ)⟧' ≫ T :=
    fun T => by rw [← Category.assoc, h6] <;> simp only [Category.assoc]
  have h7r : ∀ {V : DerivedCategory D} (T : _ ⟶ V),
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y) ≫ T
        = DerivedCategory.Q.map (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (n:ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj Y))
          ≫ ((DerivedCategory.Q).commShiftIso (n:ℤ)).hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj Y)) ≫ T :=
    fun T => by rw [← Category.assoc, h7] <;> simp only [Category.assoc]
  have h8r : ∀ {V : DerivedCategory D} (T : _ ⟶ V),
      (F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj Y))⟦(n:ℤ)⟧'
        ≫ (shiftFunctor (DerivedCategory D) (n:ℤ)).map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫ T
        = (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))⟦(n:ℤ)⟧' ≫ T :=
    fun T => by rw [← Category.assoc, h8] <;> simp only [Category.assoc]
  conv_lhs => simp only [h1r, h3r, h2r, h4r, h2'r, hdelS2, h5r, h6r, h7r, h8r, h8, Category.assoc]
  conv_rhs => simp only [hF3a, Functor.map_comp, hF3b, ShiftedHom.map, Functor.map_comp, hdelT,
    h9, Category.assoc]

end Work.SSGRoute.E0bGC
