import Mathlib
import Submission.Work.DSEQ0.cechShZ_aux

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false


open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

namespace Work.DSEQ0

universe u

/-!
# `Work.DSEQ0.qCanon_augR`

The degree-`0` compatibility of the canonical comparison `qCanon` with the augmentation
`augR` and the coaugmentation `coaugCech` of the Čech complex.

The proof is a componentwise computation.  The chain of equalities is

* `(qCanon).hom.f 0 ≫ extendXIso = Γ.map (extendXIso) ≫ (gammaComplexFull).hom.f 0`
  (`qCanon_step`): the extension comparison `extendUpNatIso` and the extension isomorphism are
  the identity in the `ℕ`-part of the degree `0` (`extendUpNatIso_comp_extendXIso`);
* `augR ≫ extendXIso = aug0` (`augR_comp_extendXIso`): the `single`-object bookkeeping cancels;
* `Γ.map (aug0) ≫ (gammaComplex.hom).f 0 = Pi.lift (fun x => Γ.map (restr (le_top)))`
  (`aug0_comp_gammaComplex_f_zero`), because `(gammaComplex.hom).f 0 = piComparison Γ _`
  (`gammaComplex_f_zero_eq`) is the product comparison of `Γ`;
* the last comparison is `psi_naturality`.
-/

private noncomputable def auxPhi {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [Limits.HasZeroObject C] [Limits.HasZeroObject D] (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℕ) (o : Option ℕ) :
    F.obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) o :=
  match o with
  | some n => Iso.refl _
  | none => IsZero.iso (F.map_isZero (isZero_zero C)) (isZero_zero D)

/-- The degree-`0` component of `extendUpNatIso`, composed with the extension isomorphism at
`0`, is `F` applied to the extension isomorphism. -/
private lemma phi_comp_XIso {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [Limits.HasZeroObject C] [Limits.HasZeroObject D] (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℕ) {o : Option ℕ} {j : ℕ} (h : o = some j) :
    (auxPhi F K o).hom ≫
      (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) h).hom
    = F.map ((HomologicalComplex.extend.XIso K h).hom) := by
  subst h
  simp only [auxPhi, Iso.refl_hom]
  rw [Category.id_comp]
  simp only [HomologicalComplex.extend.XIso, CategoryTheory.eqToIso.hom,
    CategoryTheory.eqToHom_refl, HomologicalComplex.extend.X, CategoryTheory.Functor.map_id]
  rfl

/-- The extension comparison `extendUpNatIso` is the identity in degrees lying in the image of
the embedding. -/
private lemma extendUpNatIso_comp_extendXIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Limits.HasZeroObject C] [Limits.HasZeroObject D]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) :
    (Work.DSEQ0.extendUpNatIso F K).hom.f 0 ≫
      (HomologicalComplex.extendXIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        ComplexShape.embeddingUpNat (i := 0) rfl).hom
    = F.map ((HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat (i := 0) rfl).hom) := by
  unfold Work.DSEQ0.extendUpNatIso
  dsimp only []
  rw [HomologicalComplex.Hom.isoOfComponents_hom_f _ _ 0]
  exact phi_comp_XIso F K (ComplexShape.Embedding.r_eq_some ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f (0:ℕ) = (0:ℤ)))

/-- The augmentation `augR` of the `ℤ`-indexed Čech complex restricts, in degree `0`, to the
augmentation `aug0` of the `ℕ`-indexed complex. -/
private lemma augR_comp_extendXIso (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    augR X U h ≫ (HomologicalComplex.extendXIso (cechSh X U) ComplexShape.embeddingUpNat
      (i := 0) rfl).hom = aug0 X U := by
  unfold augR augZ
  rw [HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f (augN X U h) ComplexShape.embeddingUpNat
    (i := 0) (i' := 0) rfl]
  rw [HomologicalComplex.extendSingleIso_inv_f]
  simp only [cechShPresheaf, Opposite.unop_op, Category.assoc, Category.comp_id,
    Iso.inv_hom_id, Iso.inv_hom_id_assoc]
  simp only [CochainComplex.single₀ObjXSelf, Iso.refl_inv, Category.id_comp]
  unfold augN
  rw [HomologicalComplex.mkHomFromSingle_f]
  simp only [cechShPresheaf, Opposite.unop_op, CochainComplex.single₀ObjXSelf, Iso.refl_hom,
    CochainComplex.single₀_obj_zero, Category.id_comp]

/-- The degree-`0` component of the canonical comparison `qCanon` (composed with the extension
isomorphism) is the comparison `gammaComplexFull` in degree `0`. -/
private lemma qCanon_comp_extendXIso (A : Type u) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (qCanon A X f U).hom.f 0 ≫ (HomologicalComplex.extendXIso (DSMap.cech A X f U)
        ComplexShape.embeddingUpNat (i := 0) rfl).hom
    = (extendUpNatIso (DSMap.GammaA A X f) (cechSh X U)).hom.f 0 ≫
      (HomologicalComplex.extendXIso (((DSMap.GammaA A X f).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechSh X U)) ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫
      (gammaComplexFull A X f U).hom.f 0 := by
  unfold qCanon
  rw [Iso.trans_hom, HomologicalComplex.comp_f]
  rw [show ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat A)).mapIso
      (gammaComplexFull A X f U)).hom =
      HomologicalComplex.extendMap (gammaComplexFull A X f U).hom ComplexShape.embeddingUpNat
    from rfl]
  rw [HomologicalComplex.extendMap_f (gammaComplexFull A X f U).hom ComplexShape.embeddingUpNat
    (i := 0) (i' := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- `qCanon` in degree `0`, composed with the extension isomorphism, is `gammaComplexFull` in
degree `0`. -/
private lemma qCanon_step (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (qCanon A X f U).hom.f 0 ≫ (HomologicalComplex.extendXIso (DSMap.cech A X f U)
        ComplexShape.embeddingUpNat (i := 0) rfl).hom
    = (DSMap.GammaA A X f).map ((HomologicalComplex.extendXIso (cechSh X U)
        ComplexShape.embeddingUpNat (i := 0) rfl).hom) ≫ (gammaComplexFull A X f U).hom.f 0 := by
  rw [qCanon_comp_extendXIso A X f U, ← Category.assoc,
    extendUpNatIso_comp_extendXIso]

/-- The degree-`0` component of `gammaComplex` is the product comparison of `Γ`. -/
private lemma gammaComplex_f_zero_eq (A : Type u) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (gammaComplex A X f U).hom.f 0 =
      piComparison (DSMap.GammaA A X f)
        (fun i : (Work.DSF1.Cech.E U).obj (op ⦋0⦌) |>.I =>
          (cechShPresheaf X).obj (op (Work.DSF1.Cech.Eobj U 0 i))) := by
  rfl

/-- The degree-`0` component of `gammaComplexFull`, followed by the projection to the component
`x`, is the degree-`0` component of `gammaComplex` followed by the projection and `psi`. -/
private lemma gammaComplexFull_f_zero_comp_pi (A : Type u) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens)
    (x : ((Work.DSF1.Cech.E U).obj (op ⦋0⦌)).I) :
    (gammaComplexFull A X f U).hom.f 0 ≫
      Pi.π (fun y => (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U 0 y))) x =
    (gammaComplex A X f U).hom.f 0 ≫
      Pi.π (fun y => (DSMap.GammaA A X f).obj
        ((cechShPresheaf X).obj (op (Work.DSF1.Cech.Eobj U 0 y)))) x ≫
      (Work.DSF1.Sheaf.psi A X f (Work.DSF1.Cech.Eobj U 0 x)).hom := by
  unfold gammaComplexFull
  rw [Iso.trans_hom, HomologicalComplex.comp_f, Category.assoc]
  rw [show ((cechComplexFunctor U).mapIso (gammaPresheaf A X f)).hom.f 0 ≫
        Pi.π (fun y => (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U 0 y))) x
      = ((cechComplexFunctor U).map (gammaPresheaf A X f).hom).f 0 ≫
        Pi.π (fun y => (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U 0 y))) x
    from rfl]
  rw [Work.DSF1.Cech.cechComplexFunctor_map_pi U (gammaPresheaf A X f).hom 0 x]
  rw [show (gammaPresheaf A X f).hom.app (op (Work.DSF1.Cech.Eobj U 0 x))
      = (Work.DSF1.Sheaf.psi A X f (Work.DSF1.Cech.Eobj U 0 x)).hom from rfl]
  rfl

/-- `Γ.map aug0` composed with the degree-`0` component of `gammaComplex` is the product of the
`Γ`-images of the restrictions `restr (le_top)`. -/
private lemma aug0_comp_gammaComplex_f_zero_eq (A : Type u) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (DSMap.GammaA A X f).map (aug0 X U) ≫ (gammaComplex A X f U).hom.f 0
      = Pi.lift (fun j : ((Work.DSF1.Cech.E U).obj (op ⦋0⦌)).I =>
          (DSMap.GammaA A X f).map ((cechShPresheaf X).map
            (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 j ≤ ⊤)).op)) := by
  rw [gammaComplex_f_zero_eq A X f U]
  unfold aug0
  exact map_lift_piComparison (DSMap.GammaA A X f)
    (fun i : ((Work.DSF1.Cech.E U).obj (op ⦋0⦌)).I =>
      (cechShPresheaf X).obj (op (Work.DSF1.Cech.Eobj U 0 i)))
    ((cechShPresheaf X).obj (op (⊤ : X.Opens)))
    (fun i => (cechShPresheaf X).map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 i ≤ ⊤)).op)

/-- Componentwise version of `aug0_comp_gammaComplex_f_zero_eq`. -/
private lemma aug0_comp_gammaComplex_f_zero (A : Type u) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens)
    (x : ((Work.DSF1.Cech.E U).obj (op ⦋0⦌)).I) :
    (DSMap.GammaA A X f).map (aug0 X U) ≫ (gammaComplex A X f U).hom.f 0 ≫
      Pi.π (fun y => (DSMap.GammaA A X f).obj
        ((cechShPresheaf X).obj (op (Work.DSF1.Cech.Eobj U 0 y)))) x
    = (DSMap.GammaA A X f).map ((cechShPresheaf X).map
        (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op) := by
  rw [← Category.assoc, aug0_comp_gammaComplex_f_zero_eq A X f U, Pi.lift_comp_π]

/-- Componentwise version of `aug0_comp_gammaComplex_f_zero_eq`, composed with `psi`. -/
private lemma aug0_comp_gammaComplex_f_zero_psi (A : Type u) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens)
    (x : ((Work.DSF1.Cech.E U).obj (op ⦋0⦌)).I) :
    (DSMap.GammaA A X f).map (aug0 X U) ≫ (gammaComplex A X f U).hom.f 0 ≫
      Pi.π (fun y => (DSMap.GammaA A X f).obj
        ((cechShPresheaf X).obj (op (Work.DSF1.Cech.Eobj U 0 y)))) x ≫
      (Work.DSF1.Sheaf.psi A X f (Work.DSF1.Cech.Eobj U 0 x)).hom
    = (DSMap.GammaA A X f).map ((cechShPresheaf X).map
        (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op) ≫
      (Work.DSF1.Sheaf.psi A X f (Work.DSF1.Cech.Eobj U 0 x)).hom := by
  rw [show (gammaComplex A X f U).hom.f 0 ≫
        Pi.π (fun y => (DSMap.GammaA A X f).obj
          ((cechShPresheaf X).obj (op (Work.DSF1.Cech.Eobj U 0 y)))) x ≫
        (Work.DSF1.Sheaf.psi A X f (Work.DSF1.Cech.Eobj U 0 x)).hom
      = ((gammaComplex A X f U).hom.f 0 ≫
        Pi.π (fun y => (DSMap.GammaA A X f).obj
          ((cechShPresheaf X).obj (op (Work.DSF1.Cech.Eobj U 0 y)))) x) ≫
        (Work.DSF1.Sheaf.psi A X f (Work.DSF1.Cech.Eobj U 0 x)).hom
    from (Category.assoc _ _ _).symm]
  rw [← Category.assoc, aug0_comp_gammaComplex_f_zero A X f U x]

/-- The coaugmentation of the Čech complex, followed by the projection to the component `x`, is
the restriction `restr (le_top)`. -/
private lemma coaugCech_comp_pi (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens)
    (x : ((Work.DSF1.Cech.E U).obj (op ⦋0⦌)).I) :
    coaugCech A X f U ≫
      Pi.π (fun i => (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U 0 i))) x
    = (DSMap.cechPresheaf A X f).map
        (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op := by
  have h : coaugCech A X f U =
      (Pi.lift (fun i => (DSMap.cechPresheaf A X f).map
        (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 i ≤ ⊤)).op) :
        (DSMap.cechPresheaf A X f).obj (op ⊤) ⟶
          ∏ᶜ (fun i => (DSMap.cechPresheaf A X f).obj
            (op (Work.DSF1.Cech.Eobj U 0 i)))) := rfl
  rw [h, Pi.lift_comp_π]

theorem qCanon_augR (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens)
    (h : CategoryTheory.CategoryStruct.comp (Work.DSEQ0.aug0 X U)
        ((Work.DSEQ0.cechSh X U).d 0 1) = 0) :
    CategoryTheory.CategoryStruct.comp ((DSMap.GammaA A X f).map (Work.DSEQ0.augR X U h))
        (CategoryTheory.CategoryStruct.comp ((Work.DSEQ0.qCanon A X f U).hom.f 0)
          (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
            (i := 0) rfl).hom) =
      CategoryTheory.CategoryStruct.comp (Work.DSF1.Sheaf.psi A X f (⊤ : X.Opens)).hom
        (Work.DSEQ0.coaugCech A X f U) := by
  rw [qCanon_step A X f U]
  rw [← Category.assoc, ← Functor.map_comp, augR_comp_extendXIso X U h]
  refine Pi.hom_ext (f := fun i => (DSMap.cechPresheaf A X f).obj
    (op (Work.DSF1.Cech.Eobj U 0 i))) ?_ ?_ (fun x => ?_)
  simp only [Category.assoc, gammaComplexFull_f_zero_comp_pi]
  rw [aug0_comp_gammaComplex_f_zero_psi A X f U x]
  rw [coaugCech_comp_pi A X f U x]
  rw [show (cechShPresheaf X).map
        (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op
      = Work.DSF1.Sheaf.restr (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤) from rfl]
  rw [Work.DSF1.Sheaf.psi_naturality A X f (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)]

end Work.DSEQ0
