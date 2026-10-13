import Mathlib
import Submission.Work.DSG4a.cechZBaseChangeDefs
import Submission.Work.DSF1.Cech.UnitCaseSetup
import Submission.Work.DSM5b.CechIsoDefs

/-! DSG4a: the Čech base-change comparison commutes with the differential. -/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped ChangeOfRings TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

open CategoryTheory Limits Opposite
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false

attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.power

noncomputable abbrev cechIx_aux {C : Type*} [Category C] [HasFiniteProducts C] {ι : Type*}
    (U : ι → C) (n : ℕ) :=
  ((FormalCoproduct.mk ι U).cech.obj (Opposite.op (SimplexCategory.mk n))).I

noncomputable abbrev cechOb_aux {C : Type*} [Category C] [HasFiniteProducts C] {ι : Type*}
    (U : ι → C) (n : ℕ) (x : cechIx_aux U n) : C :=
  ((FormalCoproduct.mk ι U).cech.obj (Opposite.op (SimplexCategory.mk n))).obj x

/-- Componentwise chain-map computation for the Čech complex in a completely general setting:
if a family of maps `Φ n x : F (P (E n x)) ⟶ Q (E' n x)` is compatible with the cofaces, then the
`Pi.lift`ed family commutes with the Čech differentials. -/
theorem cech_d_comm_pi_aux {C : Type*} [Category C] [HasFiniteProducts C]
    {C' : Type*} [Category C'] [HasFiniteProducts C']
    {D : Type*} [Category D] [Preadditive D] [HasProducts D]
    {D' : Type*} [Category D'] [Preadditive D'] [HasProducts D']
    (F : D ⥤ D') [F.Additive] {ι : Type*} (U : ι → C) (U' : ι → C')
    (P : Cᵒᵖ ⥤ D) (Q : C'ᵒᵖ ⥤ D')
    (Φ : ∀ (n : ℕ) (x : cechIx_aux U n),
      F.obj (P.obj (Opposite.op (cechOb_aux U n x))) ⟶ Q.obj (Opposite.op (cechOb_aux U' n x)))
    (hΦ : ∀ (n : ℕ) (a : Fin (n + 2)) (x : cechIx_aux U (n + 1)),
      F.map (P.map (((FormalCoproduct.mk ι U).cech.map
            (SimplexCategory.δ a).op).φ x).op) ≫ Φ (n + 1) x =
        Φ n (((FormalCoproduct.mk ι U).cech.map
            (SimplexCategory.δ a).op).f x) ≫
          Q.map (((FormalCoproduct.mk ι U').cech.map
            (SimplexCategory.δ a).op).φ x).op)
    (n : ℕ) (x : cechIx_aux U' (n + 1)) :
    (F.map (((cechComplexFunctor U).obj P).d n (n + 1)) ≫
        Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb_aux U (n + 1) z))) y) ≫ Φ (n + 1) y)) ≫
      Pi.π (fun y => Q.obj (Opposite.op (cechOb_aux U' (n + 1) y))) x =
    (Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb_aux U n z))) y) ≫ Φ n y) ≫
        ((cechComplexFunctor U').obj Q).d n (n + 1)) ≫
      Pi.π (fun y => Q.obj (Opposite.op (cechOb_aux U' (n + 1) y))) x := by
  have hL : (F.map (((cechComplexFunctor U).obj P).d n (n + 1)) ≫
        Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb_aux U (n + 1) z))) y) ≫ Φ (n + 1) y)) ≫
      Pi.π (fun y => Q.obj (Opposite.op (cechOb_aux U' (n + 1) y))) x =
      F.map (((cechComplexFunctor U).obj P).d n (n + 1) ≫
        Pi.π (fun z => P.obj (Opposite.op (cechOb_aux U (n + 1) z))) x) ≫ Φ (n + 1) x := by
    erw [Category.assoc, Pi.lift_comp_π, ← Category.assoc, ← Functor.map_comp]
  have hR : (Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb_aux U n z))) y) ≫ Φ n y) ≫
        ((cechComplexFunctor U').obj Q).d n (n + 1)) ≫
      Pi.π (fun y => Q.obj (Opposite.op (cechOb_aux U' (n + 1) y))) x =
      Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb_aux U n z))) y) ≫ Φ n y) ≫
        ((((cechComplexFunctor U').obj Q).d n (n + 1)) ≫
          Pi.π (fun y => Q.obj (Opposite.op (cechOb_aux U' (n + 1) y))) x) := by
    erw [Category.assoc]
  erw [hL, hR]
  erw [Work.DSM5b.cech_d_comp_π_gen U P n x]
  simp only [Functor.map_sum, Functor.map_zsmul, Functor.map_comp]
  erw [Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]
  erw [Work.DSM5b.cech_d_comp_π_gen U' Q n x]
  erw [Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro a _
  conv_lhs => erw [Category.assoc]
  conv_rhs => erw [← Category.assoc]
  erw [hΦ n a x]
  erw [Pi.lift_comp_π]
  erw [Category.assoc]
  rfl


/-! ## The comparison of a single open is natural in the open -/

/-- The base change comparison of a single Čech factor is compatible with restriction maps:
restricting a section (and base changing) is the same as base changing and then restricting. -/
theorem sectionBaseChangeA'_res_aux (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {V W : X.Opens}
    (h : V ≤ W) :
    (bcExt (A := A) (A' := A')).map ((DSMap.cechPresheaf A X f).map (homOfLE h).op) ≫
      sectionBaseChangeA' (A := A) (A' := A') X f V =
    sectionBaseChangeA' (A := A) (A' := A') X f W ≫
      (DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f)).map
        (homOfLE (show baseChangeOpen X f V ≤ baseChangeOpen X f W from
          fun _ hx => h hx)).op := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  rw [sectionBaseChangeA'_tmul, sectionBaseChangeA'_tmul]
  erw [sectionBaseChange_naturality]
  rfl

/-! ## Transporting the comparison along the identification of the two opens -/

/-- The transport step in the naturality of `bcCompE`: both composites are morphisms between the
same two objects of the thin category of opens of the base change, hence equal. -/
theorem map_resLE_eqToHom_aux (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {V W : X.Opens}
    (hh : baseChangeOpen X f V ≤ baseChangeOpen X f W)
    {Vloc Wloc : (baseChangeScheme X f).Opens}
    (hV : baseChangeOpen X f V = Vloc) (hW : baseChangeOpen X f W = Wloc)
    (ψ : Vloc ⟶ Wloc) :
    (DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f)).map (homOfLE hh).op ≫
        eqToHom (congrArg (fun U => (DSMap.cechPresheaf A' (baseChangeScheme X f)
          (baseChangeSnd X f)).obj (op U)) hV) =
      eqToHom (congrArg (fun U => (DSMap.cechPresheaf A' (baseChangeScheme X f)
          (baseChangeSnd X f)).obj (op U)) hW) ≫
        (DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f)).map ψ.op := by
  subst hV
  subst hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [Subsingleton.elim (homOfLE hh) ψ]

/-! ## Naturality of `bcCompE` with respect to the Čech cofaces -/

/-- **Naturality of the termwise comparison** with respect to the cofaces of the Čech nerve. -/
theorem bcCompE_nat_aux (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ) (a : Fin (n + 2)) (x : bcIdx U (n + 1)) :
    (bcExt (A := A) (A' := A')).map
        ((DSMap.cechPresheaf A X f).map
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ x).op) ≫
      bcCompE (A := A) (A' := A') X f U (n + 1) x =
    bcCompE (A := A) (A' := A') X f U n
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f x) ≫
      (DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f)).map
        (((Work.DSF1.Cech.E (fun i => baseChangeOpen X f (U i))).map
          (SimplexCategory.δ a).op).φ x).op := by
  have hφ : (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ x) =
      homOfLE (leOfHom (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ x)) :=
    Subsingleton.elim _ _
  rw [hφ]
  rw [bcCompE, bcCompE]
  rw [← Category.assoc, sectionBaseChangeA'_res_aux, Category.assoc,
    map_resLE_eqToHom_aux
      (V := Work.DSF1.Cech.Eobj U (n + 1) x)
      (W := Work.DSF1.Cech.Eobj U n (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f x))
      (Vloc := Work.DSF1.Cech.Eobj (fun i => baseChangeOpen X f (U i)) (n + 1) x)
      (Wloc := Work.DSF1.Cech.Eobj (fun i => baseChangeOpen X f (U i)) n
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f x))
      (hh := fun _ hy =>
        leOfHom (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ x) hy)
      (hV := (Eobj_baseChangeOpen (A := A) (A' := A') X f U (n + 1) x).symm)
      (hW := (Eobj_baseChangeOpen (A := A) (A' := A') X f U n
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f x)).symm)
      (ψ := (((Work.DSF1.Cech.E fun i => baseChangeOpen X f (U i)).map
        (SimplexCategory.δ a).op).φ x))]
  rfl

/-! ## `bcMapT` as the lift of its components -/

/-- **`bcMapT n` is the `Pi.lift` of its components.** -/
theorem bcMapT_eq_lift_aux (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (n : ℕ) :
    bcMapT (A := A) (A' := A') X f U n =
      Pi.lift (fun x : bcIdx U n =>
        (bcExt (A := A) (A' := A')).map
          (Pi.π (fun y : bcIdx U n =>
            (DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSF1.Cech.Eobj U n y))) x) ≫
        bcCompE (A := A) (A' := A') X f U n x) := by
  refine Pi.hom_ext (f := fun x : bcIdx U n =>
      (DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f)).obj
        (Opposite.op (Work.DSF1.Cech.Eobj (fun i => baseChangeOpen X f (U i)) n x))) _ _ ?_
  intro x
  rw [CategoryTheory.Limits.Pi.lift_comp_π]
  exact bcMapT_π (A := A) (A' := A') X f U n x

theorem bcMapT_comm_aux {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (n : ℕ) :
    (Work.DSG4a.bcCN (A := A) (A' := A') X f U).d n (n + 1) ≫
        Work.DSG4a.bcMapT (A := A) (A' := A') X f U (n + 1) =
      Work.DSG4a.bcMapT (A := A) (A' := A') X f U n ≫
        (Work.DSG4a.bcCT (A := A) (A' := A') X f U).d n (n + 1) := by
  rw [bcMapT_eq_lift_aux (A := A) (A' := A') X f U (n + 1),
    bcMapT_eq_lift_aux (A := A) (A' := A') X f U n]
  refine Pi.hom_ext (f := fun x : bcIdx (fun i => baseChangeOpen X f (U i)) (n + 1) =>
      (DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f)).obj
        (Opposite.op (Work.DSF1.Cech.Eobj (fun i => baseChangeOpen X f (U i)) (n + 1) x))) _ _ ?_
  intro x
  exact cech_d_comm_pi_aux (F := bcExt (A := A) (A' := A')) (U := U)
    (U' := fun i => baseChangeOpen X f (U i))
    (P := DSMap.cechPresheaf A X f)
    (Q := DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f))
    (Φ := fun n x => bcCompE (A := A) (A' := A') X f U n x)
    (hΦ := fun n a x => bcCompE_nat_aux (A := A) (A' := A') X f U n a x) n x



end Work.DSG4a
