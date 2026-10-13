import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Cech.exists_cechZ_lift

/-!
# The algebraic Čech coaugmentation as a chain map (DSF1)

The frozen statement `DSMap.area_F1_cech` of the direct summand project asks for a chain map

`cc : (single (ModuleCat A) (up ℤ) 0).obj (ModuleCat.of A A) ⟶ DSMap.cechZ A X f U`

whose degree-`0` component is the Čech coaugmentation `DSMap.coaug0` of the structure sheaf of
`X` with respect to a family of opens `U`.  This file constructs that chain map explicitly:

* `Work.DSF1.ccAug` is the `ℕ`-indexed chain map
  `(single₀ (ModuleCat A)).obj A ⟶ DSMap.cech A X f U` whose degree-`0` component is
  `DSMap.coaug0`; it exists because the coaugmentation is a cocycle
  (`Work.DSF1.Cech.coaug0_cech_d`);
* `Work.DSF1.ccZ` is its `ℤ`-indexed avatar
  `(single (ModuleCat A) (up ℤ) 0).obj (ModuleCat.of A A) ⟶ DSMap.cechZ A X f U`,
  obtained by `HomologicalComplex.extend`/`extendSingleIso` along `ComplexShape.embeddingUpNat`;
* `Work.DSF1.ccZ_compat` is the first compatibility condition of the frozen statement, a
  computation with `HomologicalComplex.extendMap_f` and `HomologicalComplex.extendSingleIso_inv_f`.
-/

namespace Work.DSF1

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Limits

universe u

/-- `ComplexShape.embeddingUpNat` fixes `0`. -/
lemma embeddingUpNat_f_zero : ComplexShape.embeddingUpNat.f (0 : ℕ) = (0 : ℤ) := by simp

/-- The Čech coaugmentation of the structure sheaf, as a chain map in `ℕ`-degrees:
`(single₀ (ModuleCat A)).obj A ⟶ DSMap.cech A X f U`. -/
noncomputable def ccAug (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) 0).obj (ModuleCat.of A A) ⟶
      DSMap.cech A X f U :=
  (CochainComplex.fromSingle₀Equiv (DSMap.cech A X f U) (ModuleCat.of A A)).symm
    ⟨DSMap.coaug0 A X f U, Work.DSF1.Cech.coaug0_cech_d A X f U⟩

/-- The degree-`0` component of `ccAug` is the Čech coaugmentation. -/
@[simp]
lemma ccAug_f_zero (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (ccAug A X f U).f 0 = DSMap.coaug0 A X f U := by
  simp only [ccAug]
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The `ℤ`-indexed Čech coaugmentation chain map. -/
noncomputable def ccZ (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A) ⟶
      DSMap.cechZ A X f U :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of A A)
      (0 : ℕ) (0 : ℤ) embeddingUpNat_f_zero).inv ≫
    HomologicalComplex.extendMap (ccAug A X f U) ComplexShape.embeddingUpNat

/-- The degree-`0` component of `ccZ`, in unfolded form. -/
lemma ccZ_f_zero (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (ccZ A X f U).f 0 =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of A A)
        (0 : ℕ) (0 : ℤ) embeddingUpNat_f_zero).inv.f 0 ≫
      (HomologicalComplex.extendMap (ccAug A X f U) ComplexShape.embeddingUpNat).f 0 :=
  rfl

/-- The degree-`0` component of `extendMap`, with the index proof fixed. -/
lemma extendMap_f_zero (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (HomologicalComplex.extendMap (ccAug A X f U) ComplexShape.embeddingUpNat).f 0 =
      (HomologicalComplex.extendXIso
          ((HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) 0).obj (ModuleCat.of A A))
          ComplexShape.embeddingUpNat embeddingUpNat_f_zero).hom ≫
        (ccAug A X f U).f 0 ≫
          (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
            embeddingUpNat_f_zero).inv :=
  HomologicalComplex.extendMap_f (ccAug A X f U) ComplexShape.embeddingUpNat
    (i := (0 : ℕ)) (i' := (0 : ℤ)) embeddingUpNat_f_zero

/-- The degree-`0` component of the inverse of `extendSingleIso`, with the index proof fixed. -/
lemma extendSingleIso_inv_f_zero (A : Type u) [CommRing A] :
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of A A)
        (0 : ℕ) (0 : ℤ) embeddingUpNat_f_zero).inv.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (ModuleCat.of A A)).inv ≫
          (HomologicalComplex.extendXIso
            ((HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) 0).obj
              (ModuleCat.of A A)) ComplexShape.embeddingUpNat embeddingUpNat_f_zero).inv :=
  HomologicalComplex.extendSingleIso_inv_f ComplexShape.embeddingUpNat (ModuleCat.of A A)
    (0 : ℕ) (0 : ℤ) embeddingUpNat_f_zero

/-- The compatibility computation in explicit form (all the objects in the statement are
written in the syntactic shape produced by `Work.DSF1.ccZ`). -/
lemma ccZ_compat_aux (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of A A)
        (0 : ℕ) (0 : ℤ) embeddingUpNat_f_zero).inv ≫
      HomologicalComplex.extendMap (ccAug A X f U) ComplexShape.embeddingUpNat).f 0 ≫
        ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0)
          embeddingUpNat_f_zero).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        DSMap.coaug0 A X f U := by
  rw [HomologicalComplex.comp_f, extendMap_f_zero, extendSingleIso_inv_f_zero]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, ccAug_f_zero]
  simp

/-- **The first compatibility condition** of the frozen `DSMap.area_F1_cech`: the degree-`0`
component of `ccZ`, transported along `HomologicalComplex.extendXIso`, is the Čech
coaugmentation. -/
theorem ccZ_compat (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (ccZ A X f U).f 0 ≫
        ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0)
          embeddingUpNat_f_zero).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        DSMap.coaug0 A X f U :=
  ccZ_compat_aux A X f U

end Work.DSF1
