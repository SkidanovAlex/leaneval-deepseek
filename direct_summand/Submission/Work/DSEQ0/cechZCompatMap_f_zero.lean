import Mathlib
import Submission.Work.DSEQ0.cechShZ_aux

set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSEQ0

universe u

theorem cechZCompatMap_f_zero (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens)
    (h : CategoryTheory.CategoryStruct.comp (Work.DSEQ0.aug0 X U)
        ((Work.DSEQ0.cechSh X U).d 0 1) = 0)
    (ψ : SheafOfModules.unit X.ringCatSheaf ≅ Work.DSF1.secSheaf (⊤ : X.Opens))
    (q : (((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Work.DSEQ0.cechShZ X U)) ≅ DSMap.cechZ A X f U) :
    CategoryTheory.CategoryStruct.comp
        ((Work.DSEQ0.cechZCompatMap (X := X) (A := A) (f := f) (U := U) (ψ := ψ) (h := h)
          (qhom := q.hom)).f 0)
        (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
          (i := 0) rfl).hom =
      CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom
        (CategoryTheory.CategoryStruct.comp (Work.DSEQ0.linA A X f)
          (CategoryTheory.CategoryStruct.comp
            ((DSMap.GammaA A X f).map (CategoryTheory.CategoryStruct.comp ψ.hom
              (Work.DSEQ0.augR X U h)))
            (CategoryTheory.CategoryStruct.comp (q.hom.f 0)
              (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
                (i := 0) rfl).hom))) :=
  -- The computation of the degree-`0` component of `cechZCompatMap` unfolds a number of
  -- semireducible definitions, so we switch to full-transparency definitional equality for the
  -- proof (the statement itself is unaffected).
  set_option backward.isDefEq.respectTransparency false in
  set_option linter.style.haveILetI false in by
  -- Unfold the comparison map and the auxiliary maps `augZTop`, `augR`, `linA`.
  letI : Algebra A ↑(X.presheaf.obj (Opposite.op ⊤)) := (DSMap.phi A X f).toAlgebra
  dsimp only [Work.DSEQ0.cechZCompatMap, Work.DSEQ0.augZTop, Work.DSEQ0.augR,
    Work.DSEQ0.linA]
  -- Degree-`0` component of a composite of chain maps.
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc]
  -- Degree-`0` components of `single.map` and of `singleMapHomologicalComplex`.
  simp only [HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Category.assoc]
  -- The two `singleObjXSelf` isomorphisms that occur here have the same (definitionally equal)
  -- object; this lets us cancel their `inv`/`hom` composites below.
  have hXYse : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A ↑(X.presheaf.obj (Opposite.op ⊤))))
      = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((DSMap.GammaA A X f).obj (SheafOfModules.unit X.ringCatSheaf))) := rfl
  rw [hXYse]
  -- Cancel `singleObjXSelf.inv ≫ singleObjXSelf.hom` (twice).
  simp only [Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc]
  simp only [Iso.inv_hom_id_assoc]

end Work.DSEQ0
