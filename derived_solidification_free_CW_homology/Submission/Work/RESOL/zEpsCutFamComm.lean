import Mathlib
import Submission.Work.RESOL.ZeroTruncSES

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

/-- Any two composites of two `eqToHom`s with the same source and target agree. -/
lemma eqToHom_comp_eqToHom_eq {C : Type*} [CategoryTheory.Category C] {X Z : C} {Y Y' : C}
    (p : X = Y) (q : Y = Z) (p' : X = Y') (q' : Y' = Z) :
    CategoryTheory.eqToHom p ≫ CategoryTheory.eqToHom q
      = CategoryTheory.eqToHom p' ≫ CategoryTheory.eqToHom q' := by
  rw [CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans]

/-- An `eqToHom` composed with the `eqToHom` of the inverse equation is an identity. -/
lemma eqToHom_comp_eqToHom_id {C : Type*} [CategoryTheory.Category C] {X Y : C}
    (p : X = Y) (q : Y = X) :
    CategoryTheory.eqToHom p ≫ CategoryTheory.eqToHom q = 𝟙 X := by
  rw [CategoryTheory.eqToHom_trans, ← CategoryTheory.eqToHom_refl X]

/-- The same identity, in right-associated form. -/
lemma eqToHom_comp_eqToHom_id_assoc {C : Type*} [CategoryTheory.Category C] {X Y Z : C}
    (p : X = Y) (q : Y = X) (f : X ⟶ Z) :
    CategoryTheory.eqToHom p ≫ CategoryTheory.eqToHom q ≫ f = f := by
  rw [← Category.assoc, eqToHom_comp_eqToHom_id, Category.id_comp]

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M))

/-! ## Transporting along an index equality -/

/-- The comparison of the terms of a homological complex along an index equality, in the
`eqToHom` form. -/
lemma XIsoOfEq_hom_eq (K : Cpx) {n m : ℤ} (h : n = m) :
    (K.XIsoOfEq h).hom = eqToHom (congrArg (fun t => K.X t) h) := rfl

/-- Composing an index transport with the differential. -/
lemma eqToHom_comp_d (K : Cpx) {n m : ℤ} (h : n = m) (p : ℤ) :
    eqToHom (congrArg (fun t => K.X t) h) ≫ K.d m p = K.d n p :=
  HomologicalComplex.XIsoOfEq_hom_comp_d K h p

/-- Composing the differential with an index transport. -/
lemma d_comp_eqToHom (K : Cpx) {n m : ℤ} (h : n = m) (p : ℤ) :
    K.d p n ≫ eqToHom (congrArg (fun t => K.X t) h) = K.d p m :=
  HomologicalComplex.d_comp_XIsoOfEq_hom K h p

/-! ## The component of `epsCutFam` on a summand -/

/-- The component formula for `epsCutFam` in "split" form: the transport into the truncation is
separated into its two `eqToHom` factors. -/
lemma epsCutFam_ι_split (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n)
    (h2 : x.1.1 = n) (h : x.1.2 = 0) :
    Sigma.ι (totFam F π hπ (geP k) B n) x ≫ epsCutFam F π hπ k B n
      = (((Rco F π hπ).obj (B.X x.1.1)).XIsoOfEq h).hom
        ≫ aug0 F π hπ (B.X x.1.1)
        ≫ eqToHom (trunc_X_of_le B k x.2.2).symm
        ≫ eqToHom (congrArg (fun t => (trunc k B).X t) h2) := by
  rw [epsCutFam_ι, dite_eq_left h]
  simp only [eqToHom_trans]

/-- The component of `epsCutFam` on a summand of positive resolution degree vanishes. -/
lemma epsCutFam_ι_zero (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n)
    (h : ¬ x.1.2 = 0) :
    Sigma.ι (totFam F π hπ (geP k) B n) x ≫ epsCutFam F π hπ k B n = 0 := by
  rw [epsCutFam_ι, dite_eq_right h]

/-- The component formula for the differential of a total complex, in the form adapted to a
composite on the right. -/
lemma totDc_comp_apply (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ)
    (y : TotIdx P n) {W : LightCondAb} (g : totX F π hπ P B (n+1) ⟶ W) :
    Sigma.ι (totFam F π hπ P B n) y ≫ (totDc F π hπ P hP B n ≫ g)
      = (totVpart F π hπ P B n y + totHpart F π hπ P hP B n y) ≫ g := by
  rw [← Category.assoc, totDc_apply]

/-! ## The two summands of the differential, followed by the augmentation -/

/-- The vertical summand of the differential, followed by the augmentation: only the summands
with resolution degree `-1` survive, and there the resolution differential meets `aug0`. -/
lemma zEpsCutFam_vert (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n) :
    totVpart F π hπ (geP k) B n x ≫ epsCutFam F π hπ k B (n+1)
      = (if h : x.1.2 + 1 = 0 then
           ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
             ≫ (((Rco F π hπ).obj (B.X x.1.1)).XIsoOfEq h).hom
             ≫ aug0 F π hπ (B.X x.1.1)
             ≫ eqToHom (trunc_X_of_le B k x.2.2).symm
             ≫ eqToHom (congrArg (fun t => (trunc k B).X t)
                 (by have h3 := x.2.1; omega : x.1.1 = n + 1))
         else 0) := by
  rw [totVpart, Category.assoc, epsCutFam_ι]
  by_cases h : x.1.2 + 1 = 0
  · rw [dite_eq_left h]
    rw [dite_eq_left (show (totVIdx x).1.2 = 0 by
      dsimp only [Work.RESOL.Zero.totVIdx]; omega)]
    simp only [Category.assoc]
    rw [eqToHom_trans]
    rfl
  · rw [dite_eq_right h]
    rw [dite_eq_right (show ¬ ((totVIdx x).1.2 = 0) by
      dsimp only [Work.RESOL.Zero.totVIdx]; omega)]
    rw [comp_zero]

/-- In resolution degree `-1` the differential of the resolution, followed by the transport to
degree `0` and the augmentation, vanishes. -/
lemma zEpsCutFam_kill (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n)
    (h : x.1.2 + 1 = 0) :
    ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
      ≫ (((Rco F π hπ).obj (B.X x.1.1)).XIsoOfEq h).hom
      ≫ aug0 F π hπ (B.X x.1.1)
      ≫ eqToHom (trunc_X_of_le B k x.2.2).symm
      ≫ eqToHom (congrArg (fun t => (trunc k B).X t)
          (by have h3 := x.2.1; omega : x.1.1 = n + 1)) = 0 := by
  rw [← Category.assoc, HomologicalComplex.d_comp_XIsoOfEq_hom]
  rw [zEpsFam_d_eq (K := (Rco F π hπ).obj (B.X x.1.1)) (j := 0)
    (W := (trunc k B).X (n+1))
    (f := aug0 F π hπ (B.X x.1.1) ≫ eqToHom (trunc_X_of_le B k x.2.2).symm
      ≫ eqToHom (congrArg (fun t => (trunc k B).X t)
          (by have h3 := x.2.1; omega : x.1.1 = n + 1)))
    (by omega : x.1.2 = -1)]
  rw [zEpsFam_aug0_d]
  rw [comp_zero]

/-- The vertical summand of the differential followed by the augmentation vanishes when the
resolution degree is `-1`. -/
lemma zEpsCutFam_vert_zero (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n)
    (h : x.1.2 + 1 = 0) :
    totVpart F π hπ (geP k) B n x ≫ epsCutFam F π hπ k B (n+1) = 0 := by
  rw [zEpsCutFam_vert, dite_eq_left h]
  exact zEpsCutFam_kill F π hπ k B n x h

/-- The vertical summand of the differential followed by the augmentation vanishes when the
resolution degree is not `-1`. -/
lemma zEpsCutFam_vert_ne (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n)
    (h : ¬ x.1.2 + 1 = 0) :
    totVpart F π hπ (geP k) B n x ≫ epsCutFam F π hπ k B (n+1) = 0 := by
  rw [zEpsCutFam_vert, dite_eq_right h]

/-- The horizontal summand of the differential, followed by the augmentation: only the summands
with resolution degree `0` survive, and there the augmentation is natural. -/
lemma zEpsCutFam_horz (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n) :
    totHpart F π hπ (geP k) (geP_step k) B n x ≫ epsCutFam F π hπ k B (n+1)
      = sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1+1))).f x.1.2
          ≫ (if h : x.1.2 = 0 then
               (((Rco F π hπ).obj (B.X (x.1.1+1))).XIsoOfEq h).hom
                 ≫ aug0 F π hπ (B.X (x.1.1+1))
                 ≫ eqToHom (trunc_X_of_le B k (le_trans x.2.2 (by omega))).symm
                 ≫ eqToHom (congrArg (fun t => (trunc k B).X t)
                     (by have h3 := x.2.1; omega : x.1.1 + 1 = n + 1))
             else 0)) := by
  rw [totHpart, Linear.units_smul_comp, Category.assoc]
  by_cases h : x.1.2 = 0
  · rw [dite_eq_left h]
    rw [epsCutFam_ι_split F π hπ k B (n+1) (totHIdx (geP_step k) x)
      (by dsimp only [Work.RESOL.Zero.totHIdx]; omega)
      (by dsimp only [Work.RESOL.Zero.totHIdx]; omega)]
    simp only [Category.assoc]
    rw [eqToHom_trans]
    rfl
  · rw [dite_eq_right h]
    rw [epsCutFam_ι_zero F π hπ k B (n+1) (totHIdx (geP_step k) x)
      (by dsimp only [Work.RESOL.Zero.totHIdx]; omega)]

/-! ## The two cases of the component identity -/

/-- The two summands of the differential of the total complex, followed by the augmentation, for a
summand of resolution degree `≠ 0`: both vanish. -/
lemma zEpsCutFam_pnz (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n)
    (h : ¬ x.1.2 = 0) :
    totVpart F π hπ (geP k) B n x ≫ epsCutFam F π hπ k B (n+1)
      + totHpart F π hπ (geP k) (geP_step k) B n x ≫ epsCutFam F π hπ k B (n+1) = 0 := by
  have hV : totVpart F π hπ (geP k) B n x ≫ epsCutFam F π hπ k B (n+1) = 0 := by
    rcases em (x.1.2 + 1 = 0) with hv | hv
    · exact zEpsCutFam_vert_zero F π hπ k B n x hv
    · exact zEpsCutFam_vert_ne F π hπ k B n x hv
  have hH : totHpart F π hπ (geP k) (geP_step k) B n x ≫ epsCutFam F π hπ k B (n+1) = 0 := by
    rw [totHpart, Linear.units_smul_comp]
    simp only [Category.assoc]
    rw [epsCutFam_ι_zero F π hπ k B (n+1) (totHIdx (geP_step k) x)
      (by dsimp only [Work.RESOL.Zero.totHIdx]; omega)]
    rw [comp_zero, smul_zero]
  rw [hV, hH, add_zero]

/-- The degree `n` component of `epsCutFam` on a summand of resolution degree `0`, followed by the
differential of the truncation, equals the two summands of the differential of the total complex
followed by `epsCutFam`. -/
lemma zEpsCutFam_p0 (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n)
    (h : x.1.2 = 0) (h2 : x.1.1 = n) :
    (((Rco F π hπ).obj (B.X x.1.1)).XIsoOfEq h).hom
        ≫ aug0 F π hπ (B.X x.1.1)
        ≫ eqToHom (trunc_X_of_le B k x.2.2).symm
        ≫ eqToHom (congrArg (fun t => (trunc k B).X t) h2)
        ≫ (trunc k B).d n (n+1)
      = totVpart F π hπ (geP k) B n x ≫ epsCutFam F π hπ k B (n+1)
        + totHpart F π hπ (geP k) (geP_step k) B n x ≫ epsCutFam F π hπ k B (n+1) := by
  have h3 : x.1.1 + 1 = n + 1 := by omega
  have hk' : k ≤ n + 1 := by omega
  rw [zEpsCutFam_vert_ne F π hπ k B n x (by omega)]
  rw [zero_add]
  rw [zEpsCutFam_horz F π hπ k B n x]
  rw [dite_eq_left h]
  have hsgn : sgn x.1.2 = 1 := by rw [sgn, h, ComplexShape.ε_zero]
  rw [hsgn, one_smul]
  simp only [Category.assoc]
  rw [eqToHom_comp_d (K := trunc k B) h2 (n+1)]
  rw [Work.RESOL.trunc_d_eq B h3 x.2.2 hk']
  rw [eqToHom_comp_eqToHom_id_assoc]
  rw [← d_comp_eqToHom (K := B) h3 x.1.1]
  rw [zEpsFam_map_smooth (φ := (Rco F π hπ).map (B.d x.1.1 (x.1.1+1)))
    (n := x.1.2) (n' := 0) h]
  rw [zEpsFam_aug0_map (F := F) (π := π) (hπ := hπ) (M := B.X x.1.1)
    (N := B.X (x.1.1+1)) (f := B.d x.1.1 (x.1.1+1))]
  have hZ : eqToHom (trunc_X_of_le B k (le_trans x.2.2 (by omega))).symm
      ≫ eqToHom (congrArg (fun t => (trunc k B).X t)
          (by have h3 := x.2.1; omega : x.1.1 + 1 = n + 1))
      = eqToHom (congrArg (fun t => B.X t) h3)
      ≫ eqToHom (trunc_X_of_le B k hk').symm :=
    eqToHom_comp_eqToHom_eq _ _ _ _
  rw [hZ]
  simp only [Category.assoc]

end Zero

/-- The degreewise augmentation `epsCutFam` of the columns `≥ k` onto the brutal truncation is a
chain map (degreewise component identity). -/
theorem zEpsCutFamComm (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M, CategoryTheory.Epi (π.app M)) (k : ℤ) (B : Work.RESOL.Cpx) {i j : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) :
    CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.epsCutFam F π hπ k B i)
        ((Work.RESOL.trunc k B).d i j)
      = CategoryTheory.CategoryStruct.comp ((Work.RESOL.Zero.totCut F π hπ k B).d i j)
          (Work.RESOL.Zero.epsCutFam F π hπ k B j) := by
  have hij' : i + 1 = j := (ComplexShape.up_Rel ℤ i j).mp hij
  subst hij'
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro x
  have hsum : x.1.2 + x.1.1 = i := x.2.1
  have hP : k ≤ x.1.1 := x.2.2
  by_cases hp0 : x.1.2 = 0
  · have h2 : x.1.1 = i := by omega
    rw [← Category.assoc, Zero.epsCutFam_ι_split F π hπ k B i x h2 hp0]
    try simp only [Category.assoc]
    rw [Zero.totCut_d_eq]
    try simp only [Category.assoc]
    rw [Zero.totDc_comp_apply F π hπ (Zero.geP k) (Zero.geP_step k) B i x]
    rw [Preadditive.add_comp]
    rw [Zero.zEpsCutFam_p0 F π hπ k B i x hp0 h2]
  · rw [← Category.assoc, Zero.epsCutFam_ι_zero F π hπ k B i x hp0]
    rw [zero_comp]
    rw [Zero.totCut_d_eq]
    try simp only [Category.assoc]
    rw [Zero.totDc_comp_apply F π hπ (Zero.geP k) (Zero.geP_step k) B i x]
    rw [Preadditive.add_comp]
    rw [Zero.zEpsCutFam_pnz F π hπ k B i x hp0]

end Work.RESOL
