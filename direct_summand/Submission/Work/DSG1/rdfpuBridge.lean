import Mathlib
import Submission.Work.DSG1.Setup

namespace Work.DSG1

open CategoryTheory

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- `singlePlusIso C M` is the identity isomorphism: the objects
`Plus.singleFunctor C 0 |>.obj M` and `Plus.Q.obj (singlePlusObj C M)` are definitionally equal,
and every structural isomorphism entering the definition of `singlePlusIso` is the identity. -/
lemma singlePlusIso_eq_refl {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] (M : C) :
    singlePlusIso C M = Iso.refl ((DerivedCategory.Plus.singleFunctor C 0).obj M) := by
  apply Iso.ext
  apply DerivedCategory.Plus.ι.map_injective
  simp only [singlePlusIso]
  rw [Functor.FullyFaithful.preimageIso_hom, ObjectProperty.ι_map]
  simp only [DerivedCategory.Plus.singleFunctorιIso, DerivedCategory.singleFunctorIsoCompQ,
    DerivedCategory.Plus.QCompιIso, ObjectProperty.liftCompιIso]
  simp

/-- The components of `DerivedCategory.Plus.quotientCompQhIso C` are the identities, because
`DerivedCategory.quotientCompQhIso C` is `Quotient.lift.isLift`, whose components are all
`Iso.refl`. -/
lemma quotientCompQhIso_hom_app_eq_id {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex.Plus C) :
    (DerivedCategory.Plus.quotientCompQhIso C).hom.app K =
      𝟙 (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj K)) :=
  rfl

/-- The components of the inverse of `DerivedCategory.Plus.quotientCompQhIso C` are the
identities. -/
lemma quotientCompQhIso_inv_app_eq_id {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex.Plus C) :
    (DerivedCategory.Plus.quotientCompQhIso C).inv.app K =
      𝟙 (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj K)) :=
  rfl

/-- The unit of the right derived functor at a one-term complex is the homotopy level unit at
the corresponding object of the bounded below homotopy category. -/
lemma rightDerivedFunctorPlusUnit_app_singlePlus {C : Type*} [Category* C] [Abelian C]
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] (M : C) :
    F.rightDerivedFunctorPlusUnit.app (singlePlusObj C M) =
      F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient C).obj (singlePlusObj C M)) := by
  rw [Functor.rightDerivedFunctorPlusUnit_app]
  have hD : F.rightDerivedFunctorPlus.map
        ((𝟙 (DerivedCategory.Plus.Q.obj (singlePlusObj C M)) :
          DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj (singlePlusObj C M)) ⟶
            DerivedCategory.Plus.Q.obj (singlePlusObj C M))) =
      𝟙 (F.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj (singlePlusObj C M)))) := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [show (DerivedCategory.Plus.quotientCompQhIso C).hom.app (singlePlusObj C M) =
      (𝟙 (DerivedCategory.Plus.Q.obj (singlePlusObj C M)) :
        DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj (singlePlusObj C M)) ⟶
          DerivedCategory.Plus.Q.obj (singlePlusObj C M)) from rfl]
  rw [hD]
  erw [Category.comp_id]
  erw [Category.id_comp]
  simp only [Functor.quotientCompMapHomotopyCategoryPlusIso, Iso.refl_inv, NatTrans.id_app]
  erw [DerivedCategory.Plus.Qh.map_id]
  erw [Category.id_comp]

/-- The canonical isomorphism `singleFunctorMapHomotopyCategoryPlus F 0` is compatible with the
complex-level identification `mapSinglePlusIso F M`: on the bounded below homotopy categories, its
inverse is the image under the quotient functor of the inverse of `mapSinglePlusIso F M`. -/
lemma singleFunctorMapHomotopyCategoryPlus_inv_app {C : Type*} [Category* C] [Abelian C]
    {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive] (M : C) :
    (LeanEval.AlgebraicGeometry.DirectSummand.singleFunctorMapHomotopyCategoryPlus F 0).inv.app M =
      (HomotopyCategory.Plus.quotient D).map ((mapSinglePlusIso F M).inv) := by
  apply (HomotopyCategory.Plus.ι D).map_injective
  have hmsp : (CochainComplex.Plus.ι D).map ((mapSinglePlusIso F M).inv) =
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M := by
    rw [show (CochainComplex.Plus.ι D).map ((mapSinglePlusIso F M).inv) =
        (mapSinglePlusIso F M).inv.hom from rfl]
    rw [show (mapSinglePlusIso F M).inv.hom =
        ((Functor.mapCochainComplexPlusCompι F).app (singlePlusObj C M) ≪≫
          (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M).inv
        from rfl]
    rw [show ((Functor.mapCochainComplexPlusCompι F).app (singlePlusObj C M)) = Iso.refl _ from rfl]
    rw [Iso.trans_inv, Iso.refl_inv]
    exact Category.comp_id _
  rw [show (HomotopyCategory.Plus.ι D).map
        ((LeanEval.AlgebraicGeometry.DirectSummand.singleFunctorMapHomotopyCategoryPlus F 0).inv.app M) =
      (LeanEval.AlgebraicGeometry.DirectSummand.singleFunctorMapHomotopyCategory F 0).inv.app M from rfl]
  rw [show (HomotopyCategory.Plus.ι D).map
        ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlusIso F M).inv)) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((CochainComplex.Plus.ι D).map ((mapSinglePlusIso F M).inv)) from rfl]
  rw [hmsp]
  rw [show (LeanEval.AlgebraicGeometry.DirectSummand.singleFunctorMapHomotopyCategory F 0).inv.app M =
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).associator
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)) (F.mapHomotopyCategory (ComplexShape.up ℤ)) ≪≫
        (HomologicalComplex.single C (ComplexShape.up ℤ) 0).isoWhiskerLeft
            (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) ≪≫
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).associator
                (F.mapHomologicalComplex (ComplexShape.up ℤ))
                (HomotopyCategory.quotient D (ComplexShape.up ℤ))).symm ≪≫
            Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0)
              (HomotopyCategory.quotient D (ComplexShape.up ℤ))).inv.app M from rfl]
  rw [Iso.trans_inv, Iso.trans_inv, Iso.trans_inv]
  simp only [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Category.assoc, Functor.associator_inv_app,
    Functor.associator_hom_app, Iso.symm_inv, Category.comp_id, Category.id_comp]
  rw [show (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) = 𝟙 _ from rfl]
  simp

/-
**Bridge between the `single_0` level unit of `ChallengeDeps` and the complex level unit.**

`rightDerivedFunctorPlusUnit' F 0` (`ChallengeDeps`) is the `single_0` level unit
`F ⋙ Plus.singleFunctor D 0 ⟶ Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus`; the complex
level unit `F.rightDerivedFunctorPlusUnit` is the natural transformation
`F.mapCochainComplexPlus ⋙ Plus.Q ⟶ Plus.Q ⋙ F.rightDerivedFunctorPlus`.  The statement says
that they agree, after transporting along the canonical isomorphisms `singlePlusIso` (from
`Submission.Work.DSG1.Setup`, `Σ_C M ≅ Q (singlePlusObj C M)`) and `mapSinglePlusIso`
(`F.mapCochainComplexPlus.obj (singlePlusObj C M) ≅ singlePlusObj D (F M)`).

Both sides are built from `Functor.rightDerivedFunctorPlusUnith`, `Plus.Qh` and the same
`singleFunctorMapHomotopyCategoryPlus` isomorphism; the proof should be a diagram chase using
`DerivedCategory.Plus.quotientCompQhIso`, `DerivedCategory.Plus.singleFunctorιIso`,
`DerivedCategory.Plus.QCompιIso`, `HomotopyCategory.Plus.singleFunctorιIso` and
`DerivedCategory.Plus.isIso_iff` (isomorphisms in `D⁺ C` can be checked after applying `Plus.ι`,
which is fully faithful: `ObjectProperty.fullyFaithfulι`).
-/

theorem rdfpuBridge {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    (M : C) :
    (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' F 0).app M =
      (Work.DSG1.singlePlusIso D (F.obj M)).hom ≫
        (DerivedCategory.Plus.Q).map ((Work.DSG1.mapSinglePlusIso F M).inv) ≫
          F.rightDerivedFunctorPlusUnit.app (Work.DSG1.singlePlusObj C M) ≫
            F.rightDerivedFunctorPlus.map ((Work.DSG1.singlePlusIso C M).inv) := by
  have hL : (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' F 0).app M =
      DerivedCategory.Plus.Qh.map
          ((LeanEval.AlgebraicGeometry.DirectSummand.singleFunctorMapHomotopyCategoryPlus F 0).inv.app M) ≫
        F.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.singleFunctor C 0).obj M) := rfl
  rw [hL]
  rw [rightDerivedFunctorPlusUnit_app_singlePlus F M]
  rw [singlePlusIso_eq_refl (C := D) (F.obj M), singlePlusIso_eq_refl (C := C) M]
  erw [Iso.refl_hom]
  erw [Category.id_comp]
  erw [Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  rw [show (DerivedCategory.Plus.Q).map ((mapSinglePlusIso F M).inv) =
      DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlusIso F M).inv)) from rfl]
  rw [← singleFunctorMapHomotopyCategoryPlus_inv_app F M]
  rfl

end Work.DSG1
