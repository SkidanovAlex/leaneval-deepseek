import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.CechSheafRestr
import Submission.Work.DSMX0bU.cechTrivAll_of_le_mem
import Submission.Work.DSF1.Sheaf.FHCCDesign
import Submission.Work.DSF1.Cech.isIsoDeletion_Qo
import Submission.Work.DSF1.Cech.DeltaSuccK

/-!
# Exactness of the Čech complex of the restriction of a presheaf along an open

Let `X` be a scheme, `U : ι → X.Opens` a family of opens, `i₀ : ι`, `W : X.Opens` with
`W ≤ U i₀`, and `P` a presheaf of abelian groups.  We show that the Čech complex of the
family `U` with coefficients the restriction `V ↦ P (V ⊓ W)` has trivial cohomology in
positive degrees.

The complex is contractible: inserting `i₀` at position `0` of a simplex does not change
the open `E n x ⊓ W`, because `E (n+1) (insert i₀ x) = E n x ⊓ U i₀` and `W ≤ U i₀`; hence
the cofaces that insert `i₀` are isomorphisms of the coefficient presheaf.  The general
machinery of `Work.DSF1.Cech` (`k`, `DeltaSuccK`, `homotopy_succ`) is reproduced here over
`AddCommGrpCat` (rather than `ModuleCat R`), and then fed to
`Work.DSMX0bU.cechTrivAll_of_contractible`.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators
open Work.DSF1.Cech

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}

/-! ## The Čech cosimplicial object over `AddCommGrpCat` -/

/-- The cosimplicial object whose alternating coface complex is the Čech complex of the
family `U` with coefficients `Q`. -/
noncomputable abbrev CosiAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    CosimplicialObject (AddCommGrpCat.{u}) :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj Q

/-- The coface maps of the Čech cosimplicial object, re-typed as morphisms of the Čech
complex. -/
noncomputable def deltaXAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (i : Fin (n+2)) :
    ((cechComplexFunctor U).obj Q).X n ⟶ ((cechComplexFunctor U).obj Q).X (n+1) :=
  (CosiAb U Q).δ i

/-- The coefficient presheaf `Q` inverts all coface maps of the Čech nerve which insert
the index `i₀`. -/
def IsIsoDelAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (i₀ : ι) : Prop :=
  ∀ (n : ℕ) (x : ((E U).obj (op ⦋n⦌)).I),
    IsIso (Q.map (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).op)

/-- The `y`-th component of the coface `δ i` of the Čech cosimplicial object. -/
lemma cech_delta_comp_πAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (i : Fin (n+2)) (y : ((E U).obj (op ⦋n+1⦌)).I) :
    (CosiAb U Q).δ i ≫
        Pi.π (fun y : ((E U).obj (op ⦋n+1⦌)).I => Q.obj (op (Eobj U (n+1) y))) y =
      Pi.π (fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z)))
          (((E U).map (SimplexCategory.δ i).op).f y) ≫
        Q.map (((E U).map (SimplexCategory.δ i).op).φ y).op := by
  show Pi.lift _ ≫ Pi.π _ y = _
  exact Pi.lift_comp_π _ _

/-! ## The contracting homotopy -/

/-- The contracting homotopy of the Čech complex in degree `n`: project to the index
obtained by inserting `i₀` and apply the inverse of the (iso) coface map. -/
noncomputable def kAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {i₀ : ι} (h : IsIsoDelAb U Q i₀) (n : ℕ) :
    ((cechComplexFunctor U).obj Q).X (n+1) ⟶ ((cechComplexFunctor U).obj Q).X n :=
  Pi.lift (f := fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z)))
    (fun x => Pi.π (fun y : ((E U).obj (op ⦋n+1⦌)).I => Q.obj (op (Eobj U (n+1) y)))
        (insIdx U i₀ n x) ≫
          @inv _ _ _ _ (Q.map (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).op)
            (h n x))

/-- The `x`-th component of the homotopy `kAb n`. -/
lemma kAb_comp_π (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {i₀ : ι} (h : IsIsoDelAb U Q i₀) (n : ℕ) (x : ((E U).obj (op ⦋n⦌)).I) :
    kAb U Q h n ≫ Pi.π (fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z))) x =
      Pi.π (fun y : ((E U).obj (op ⦋n+1⦌)).I => Q.obj (op (Eobj U (n+1) y)))
        (insIdx U i₀ n x) ≫
          @inv _ _ _ _ (Q.map (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).op)
            (h n x) := by
  simp only [kAb, Pi.lift_comp_π]

/-- The "extra codegeneracy" identity `δ₀ ≫ kAb = 𝟙` in degree `n`. -/
lemma delta0_comp_kAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {i₀ : ι} (h : IsIsoDelAb U Q i₀) (n : ℕ) :
    (CosiAb U Q).δ (0 : Fin (n+2)) ≫ kAb U Q h n = 𝟙 _ := by
  apply Pi.hom_ext
  intro x
  show ((CosiAb U Q).δ (0 : Fin (n+2)) ≫ kAb U Q h n) ≫
      Pi.π (f := fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z))) x =
    Pi.π (f := fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z))) x
  rw [Category.assoc, kAb_comp_π, ← Category.assoc, cech_delta_comp_πAb]
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-! ## The second simplicial identity -/

/-- The simplicial identity `δ (i.succ) ≫ kAb = kAb ≫ δ i`. -/
lemma DeltaSuccAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {i₀ : ι}
    (h : IsIsoDelAb U Q i₀) (n : ℕ) (i : Fin (n+2)) :
    CategoryTheory.CategoryStruct.comp (CosimplicialObject.δ (CosiAb U Q) i.succ)
        (kAb U Q h (n+1))
      = CategoryTheory.CategoryStruct.comp (kAb U Q h n)
        (CosimplicialObject.δ (CosiAb U Q) i) := by
  apply Pi.hom_ext
  intro y
  change CategoryStruct.comp
        (CategoryStruct.comp (CosimplicialObject.δ (CosiAb U Q) i.succ) (kAb U Q h (n+1)))
        (Pi.π (fun z => Q.obj (op (Eobj U (n+1) z))) y)
      = CategoryStruct.comp
        (CategoryStruct.comp (kAb U Q h n) (CosimplicialObject.δ (CosiAb U Q) i))
        (Pi.π (fun z => Q.obj (op (Eobj U (n+1) z))) y)
  conv_lhs =>
    rw [Category.assoc, kAb_comp_π U Q h (n+1) y, ← Category.assoc,
        cech_delta_comp_πAb U Q (n+1) i.succ (insIdx U i₀ (n+1) y), Category.assoc]
  conv_rhs =>
    rw [Category.assoc, cech_delta_comp_πAb U Q n i y, ← Category.assoc,
        kAb_comp_π U Q h n (((E U).map (SimplexCategory.δ i).op).f y), Category.assoc]
  have hZ : ((E U).map (SimplexCategory.δ i.succ).op).f (insIdx U i₀ (n+1) y)
      = insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y) := InsIdxDelta U i₀ n i y
  have hpi : Pi.π (fun z => Q.obj (op (Eobj U (n+1) z)))
        (((E U).map (SimplexCategory.δ i.succ).op).f (insIdx U i₀ (n+1) y)) ≫
      eqToHom (congrArg (fun z => Q.obj (op (Eobj U (n+1) z))) hZ) =
      Pi.π (fun z => Q.obj (op (Eobj U (n+1) z)))
        (insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y)) :=
    deltaSucc_pi_π_eqToHom (fun z => Q.obj (op (Eobj U (n+1) z))) hZ
  let f1 : Eobj U (n+2) (insIdx U i₀ (n+1) y) ⟶ Eobj U (n+1) y :=
    ((E U).map (SimplexCategory.δ (0 : Fin (n+3))).op).φ (insIdx U i₀ (n+1) y)
  let f2 : Eobj U (n+2) (insIdx U i₀ (n+1) y) ⟶
      Eobj U (n+1) (((E U).map (SimplexCategory.δ i.succ).op).f (insIdx U i₀ (n+1) y)) :=
    ((E U).map (SimplexCategory.δ i.succ).op).φ (insIdx U i₀ (n+1) y)
  let fi : Eobj U (n+1) y ⟶ Eobj U n (((E U).map (SimplexCategory.δ i).op).f y) :=
    ((E U).map (SimplexCategory.δ i).op).φ y
  let g0 : Eobj U (n+1) (insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y)) ⟶
      Eobj U n (((E U).map (SimplexCategory.δ i).op).f y) :=
    ((E U).map (SimplexCategory.δ (0 : Fin (n+2))).op).φ
      (insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y))
  have hsq : f1 ≫ fi = f2 ≫ (eqToHom (congrArg (Eobj U (n+1)) hZ) ≫ g0) :=
    Subsingleton.elim _ _
  haveI i1 : IsIso (Q.map f1.op) := h (n+1) y
  haveI i0 : IsIso (Q.map g0.op) := h n (((E U).map (SimplexCategory.δ i).op).f y)
  haveI : IsIso (Q.map (eqToHom (congrArg (Eobj U (n+1)) hZ) ≫ g0).op) := by
    rw [op_comp, Q.map_comp]; infer_instance
  have hkey := deltaSucc_inv_nat Q f1 f2 fi (eqToHom (congrArg (Eobj U (n+1)) hZ) ≫ g0) hsq
  have hkm : Q.map (eqToHom (congrArg (Eobj U (n+1)) hZ) ≫ g0).op
      = Q.map g0.op ≫ Q.map (eqToHom (congrArg (Eobj U (n+1)) hZ)).op := by
    rw [op_comp, Q.map_comp]
  have hEB : inv (Q.map (eqToHom (congrArg (Eobj U (n+1)) hZ)).op)
      = eqToHom (congrArg (fun z => Q.obj (op (Eobj U (n+1) z))) hZ) := by
    rw [deltaSucc_inv_map_eqToHom_op]
  have core : Q.map f2.op ≫ inv (Q.map f1.op)
      = eqToHom (congrArg (fun z => Q.obj (op (Eobj U (n+1) z))) hZ)
          ≫ inv (Q.map g0.op) ≫ Q.map fi.op := by
    simp only [hkey, hkm, IsIso.inv_comp, Category.assoc, hEB]
  change Pi.π (fun z => Q.obj (op (Eobj U (n+1) z)))
        (((E U).map (SimplexCategory.δ i.succ).op).f (insIdx U i₀ (n+1) y)) ≫
      (Q.map f2.op ≫ inv (Q.map f1.op)) =
    Pi.π (fun z => Q.obj (op (Eobj U (n+1) z)))
        (insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y)) ≫
      (inv (Q.map g0.op) ≫ Q.map fi.op)
  rw [← hpi, core, Category.assoc]

/-! ## The chain homotopy identities -/

/-- The differential of the Čech complex is the alternating sum of its cofaces. -/
lemma d_eq_sum_deltaAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    ((cechComplexFunctor U).obj Q).d n (n+1) =
      ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • deltaXAb U Q n i :=
  (CochainComplex.of_d (fun m => (CosiAb U Q).obj (SimplexCategory.mk m))
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (CosiAb U Q)) n).trans rfl

/-- `δ₀ ≫ kAb = 𝟙`, in `X`-types. -/
lemma delta0_comp_kAb_dX (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {i₀ : ι} (h : IsIsoDelAb U Q i₀) (n : ℕ) :
    deltaXAb U Q n 0 ≫ kAb U Q h n = 𝟙 _ :=
  delta0_comp_kAb U Q h n

/-- `δ_{i+1} ≫ kAb = kAb ≫ δ_i`, in `X`-types. -/
lemma DeltaSuccAb_dX (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {i₀ : ι} (h : IsIsoDelAb U Q i₀) (n : ℕ) (i : Fin (n+2)) :
    deltaXAb U Q (n+1) i.succ ≫ kAb U Q h (n+1) = kAb U Q h n ≫ deltaXAb U Q n i :=
  DeltaSuccAb U Q h n i

/-- **Chain homotopy identity in degree `n + 1`.** -/
lemma homotopy_succAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {i₀ : ι} (h : IsIsoDelAb U Q i₀) (n : ℕ) :
    kAb U Q h n ≫ ((cechComplexFunctor U).obj Q).d n (n+1) +
      ((cechComplexFunctor U).obj Q).d (n+1) (n+2) ≫ kAb U Q h (n+1) =
        𝟙 (((cechComplexFunctor U).obj Q).X (n+1)) := by
  rw [d_eq_sum_deltaAb U Q n, d_eq_sum_deltaAb U Q (n+1)]
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  rw [Fin.sum_univ_succ (n := n+2)]
  rw [Fin.val_zero, pow_zero, one_zsmul, delta0_comp_kAb_dX U Q h (n+1)]
  have hh : (∑ x : Fin (n+2), (-1 : ℤ) ^ (x : ℕ) • (kAb U Q h n ≫ deltaXAb U Q n x)) +
      (∑ i : Fin (n+2), (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) •
          (deltaXAb U Q (n+1) i.succ ≫ kAb U Q h (n+1))) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [DeltaSuccAb_dX U Q h n i,
      show (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) = -((-1 : ℤ) ^ (i : ℕ)) from by
        simp [Fin.val_succ, pow_succ]]
    rw [neg_zsmul, add_neg_cancel]
  rw [show (∑ x : Fin (n+2), (-1 : ℤ) ^ (x : ℕ) • (kAb U Q h n ≫ deltaXAb U Q n x)) +
        (𝟙 (((cechComplexFunctor U).obj Q).X (n+1)) +
          ∑ i : Fin (n+2), (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) •
            (deltaXAb U Q (n+1) i.succ ≫ kAb U Q h (n+1)))
      = ((∑ x : Fin (n+2), (-1 : ℤ) ^ (x : ℕ) • (kAb U Q h n ≫ deltaXAb U Q n x)) +
          (∑ i : Fin (n+2), (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) •
            (deltaXAb U Q (n+1) i.succ ≫ kAb U Q h (n+1)))) +
          𝟙 (((cechComplexFunctor U).obj Q).X (n+1)) from by abel,
    hh, zero_add]

/-! ## The restriction presheaf and the main result -/

/-- The restriction presheaf `V ↦ P (V ⊓ W)` inverts the cofaces inserting `i₀`,
when `W ≤ U i₀`. -/
lemma isIsoDelAb_restrP (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) (i₀ : ι) (hW : W ≤ U i₀) :
    IsIsoDelAb U (restrP P W) i₀ := by
  intro n x
  have hf : Eobj U n (((E U).map (SimplexCategory.δ 0).op).f (insIdx U i₀ n x)) = Eobj U n x :=
    congrArg (Eobj U n) (cech_map_delta0_f U i₀ n x)
  have hfmap : (restrP P W).map
      ((((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).op) =
      P.map (homOfLE (inf_le_inf_right W
        (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).le)).op := rfl
  rw [hfmap]
  have h : Eobj U (n+1) (insIdx U i₀ n x) ⊓ W =
      Eobj U n (((E U).map (SimplexCategory.δ 0).op).f (insIdx U i₀ n x)) ⊓ W := by
    rw [Eobj_insIdx U i₀ n x, hf, inf_assoc, inf_eq_right.mpr hW]
  have hg : IsIso (homOfLE (inf_le_inf_right W
      (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).le)) :=
    homOfLE_isIso_of_eq _ h
  have hg' : IsIso ((homOfLE (inf_le_inf_right W
      (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).le)).op) :=
    (isIso_op_iff _).mpr hg
  exact @Functor.map_isIso _ _ _ _ _ _ P _ hg'

theorem cechTrivAll_local {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (i₀ : ι) (W : X.Opens) (hW : W ≤ U i₀)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})) :
    Work.DSF1.Sheaf.CechTrivAll ((Work.DSF1.Sheaf.cechComplexP U P).obj (Opposite.op W)) := by
  have h : IsIsoDelAb U (restrP P W) i₀ := isIsoDelAb_restrP U P W i₀ hW
  exact Work.DSMX0bU.cechTrivAll_of_contractible (kAb U (restrP P W) h)
    (homotopy_succAb U (restrP P W) h)

end Work.DSF1.Sheaf
