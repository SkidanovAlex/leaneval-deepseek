import Mathlib
import Submission.Work.DSEQ0.cechShZ_aux
import Submission.Work.DSEQ0.psiUnit
import Submission.Work.DSEQ0.linA_psiUnitHom_psi_proof
import Submission.Work.DSEQ0.qCanon_augR
import Submission.Work.DSEQ0.cechZCompatMap_f_zero

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSEQ0

universe u

/-- The coaugmentation of the challenge's Čech complex is `unitTop` followed by the
coaugmentation of the section presheaf: `DSMap.coaug0` is the `Pi.lift` of
`unitTop ≫ cechPresheaf.map (homOfLE le_top).op`. -/
lemma unitTop_coaugCech_eq_coaug0 (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    DSMap.unitTop A X f ≫ coaugCech A X f U = DSMap.coaug0 A X f U := by
  dsimp only [DSMap.coaug0, coaugCech, Work.DSF1.Cech.coaug]
  refine Limits.Pi.hom_ext _ _ (fun x => ?_)
  rw [Category.assoc]
  rw [Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π]

theorem cechShZ_compat (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (h : CategoryTheory.CategoryStruct.comp (Work.DSEQ0.aug0 (X := X) (U := U))
      ((Work.DSEQ0.cechSh (X := X) (U := U)).d 0 1) = 0) :
    ∃ (ψ : CategoryTheory.Iso (SheafOfModules.unit X.ringCatSheaf)
        (Work.DSF1.secSheaf (⊤ : X.Opens)))
      (q : CategoryTheory.Iso
        (((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (Work.DSEQ0.cechShZ (X := X) (U := U)))
        (DSMap.cechZ A X f U)),
      CategoryTheory.CategoryStruct.comp
          ((Work.DSEQ0.cechZCompatMap (A := A) (X := X) (f := f) (U := U) (ψ := ψ) (h := h)
            (qhom := q.hom)).f 0)
          ((HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
            (i := 0) rfl).hom) =
        CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom
          (DSMap.coaug0 A X f U) := by
  refine ⟨psiUnit X, qCanon A X f U, ?_⟩
  rw [cechZCompatMap_f_zero A X f U h (psiUnit X) (qCanon A X f U)]
  refine (cancel_epi (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (ModuleCat.of A A)).hom).mp ?_
  have key : CategoryTheory.CategoryStruct.comp (linA A X f)
      (CategoryTheory.CategoryStruct.comp
        ((DSMap.GammaA A X f).map (CategoryTheory.CategoryStruct.comp (psiUnit X).hom
          (augR X U h)))
        (CategoryTheory.CategoryStruct.comp ((qCanon A X f U).hom.f 0)
          (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
            (i := 0) rfl).hom)) = DSMap.coaug0 A X f U := by
    have h1 : CategoryTheory.CategoryStruct.comp (linA A X f)
        (CategoryTheory.CategoryStruct.comp
          ((DSMap.GammaA A X f).map (CategoryTheory.CategoryStruct.comp (psiUnit X).hom
            (augR X U h)))
          (CategoryTheory.CategoryStruct.comp ((qCanon A X f U).hom.f 0)
            (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
              (i := 0) rfl).hom)) =
        CategoryTheory.CategoryStruct.comp (linA A X f)
          (CategoryTheory.CategoryStruct.comp ((DSMap.GammaA A X f).map (psiUnit X).hom)
            (CategoryTheory.CategoryStruct.comp ((DSMap.GammaA A X f).map (augR X U h))
              (CategoryTheory.CategoryStruct.comp ((qCanon A X f U).hom.f 0)
                (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
                  (i := 0) rfl).hom))) := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    rw [h1, show (psiUnit X).hom = psiUnitHom X from rfl,
      qCanon_augR A X f U h]
    have h2 : CategoryTheory.CategoryStruct.comp (linA A X f)
        (CategoryTheory.CategoryStruct.comp ((DSMap.GammaA A X f).map (psiUnitHom X))
          (CategoryTheory.CategoryStruct.comp
            (Work.DSF1.Sheaf.psi A X f (⊤ : X.Opens)).hom (coaugCech A X f U))) =
        CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CategoryStruct.comp (linA A X f)
            (CategoryTheory.CategoryStruct.comp ((DSMap.GammaA A X f).map (psiUnitHom X))
              (Work.DSF1.Sheaf.psi A X f (⊤ : X.Opens)).hom)) (coaugCech A X f U) := by
      simp only [Category.assoc]
    rw [h2, linA_psiUnitHom_psi_proof A X f]
    exact unitTop_coaugCech_eq_coaug0 A X f U
  exact key

end Work.DSEQ0
