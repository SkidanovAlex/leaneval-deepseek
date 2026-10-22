import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.B5Setup
import Submission.Work.RESOL.solidCofibrant_single_atomic

/-!
AREA RESOL — the induction step of B5: `solidCofibrant_trunc`.

Given a complex `K` of atoms and `j : ℤ`, we show that the brutal truncation `trunc (j-1) K`
is solid-cofibrant as soon as `trunc j K` is.  The proof goes through the **degreewise split
short exact sequence of complexes**

`0 ⟶ trunc j K ⟶ trunc (j-1) K ⟶ single (j-1) (K.X (j-1)) ⟶ 0`,

whose middle term `trunc (j-1) K` has the terms of `K` in degrees `≥ j-1` and vanishes below,
and whose third term is the single complex on the new term `K.X (j-1)` in degree `j-1`.
By `CochainComplex.trianglehOfDegreewiseSplit` (with the degreewise splittings
`truncSplitting`), this short exact sequence gives a distinguished triangle of
`K(LightCondAb)` isomorphic — after one inverse rotation — to

`(single (j-1) (K.X (j-1)))⟦-1⟧ ⟶ trunc j K ⟶ trunc (j-1) K`.

Since free objects on light profinite sets are solid-cofibrant (`AtomProp`, via the
coproduct closure applied to the atomic sum `K.X (j-1)`, see
`RESOL/solidCofibrant_single_atomic.lean`), and since solid-cofibrant complexes are closed
under shifts, mapping cones and isomorphisms in `K(LightCondAb)` (the structure
`CofibrantClosure`), the third object of this triangle — namely `trunc (j-1) K` — is
solid-cofibrant.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.RESOL

/-! ## Elementary cancellation lemmas for `eqToHom` -/

lemma eqToHom_comp_eqToHom_self {C : Type*} [Category C] {X Y : C} (p : X = Y) (q : Y = X) :
    eqToHom p ≫ eqToHom q = 𝟙 X := by
  rw [eqToHom_trans, eqToHom_refl]

lemma eqToHom_comp_eqToHom_self_sandwich {C : Type*} [Category C] {X Y Z : C}
    (p : X = Y) (q : Y = X) (f : X ⟶ Z) : eqToHom p ≫ eqToHom q ≫ f = f := by
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-! ## Degreewise description of `trunc` -/

lemma trunc_X_of_le (K : Cpx) (m : ℤ) {n : ℤ} (h : m ≤ n) : (trunc m K).X n = K.X n := by
  simp only [trunc, if_pos h]

lemma trunc_X_of_not_le (K : Cpx) (m : ℤ) {n : ℤ} (h : ¬ m ≤ n) : (trunc m K).X n = 0 := by
  simp only [trunc, if_neg h]

lemma isZero_trunc_X (K : Cpx) (m : ℤ) {n : ℤ} (h : ¬ m ≤ n) : IsZero ((trunc m K).X n) := by
  rw [trunc_X_of_not_le K m h]
  exact isZero_zero LightCondAb

lemma trunc_pred_le (j : ℤ) : j - 1 ≤ j := by omega

/-- Inside the truncation range, the differential of `trunc m K` is conjugate to the
differential of `K` by the canonical identifications of the terms. -/
lemma trunc_d_eq (K : Cpx) {m i n : ℤ} (hin : i + 1 = n) (h : m ≤ i) (h' : m ≤ n) :
    (trunc m K).d i n =
      eqToHom (trunc_X_of_le K m h) ≫ K.d i n ≫ eqToHom (trunc_X_of_le K m h').symm := by
  rw [conj_eqToHom_iff_heq ((trunc m K).d i n) (K.d i n) (trunc_X_of_le K m h)
    (trunc_X_of_le K m h')]
  simp only [trunc, dif_pos (show m ≤ i ∧ m ≤ n ∧ i + 1 = n from ⟨h, h', hin⟩),
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  try rfl

/-- The differential of `trunc m K` vanishes below the truncation range. -/
lemma trunc_d_eq_zero (K : Cpx) {m i n : ℤ} (hin : i + 1 = n) (h : ¬ m ≤ i) :
    (trunc m K).d i n = 0 := by
  simp only [trunc]
  exact dite_eq_right (show ¬ (m ≤ i ∧ m ≤ n ∧ i + 1 = n) from by
    rintro ⟨h1, _⟩
    exact h h1)

/-! ## The inclusion `trunc j K ⟶ trunc (j-1) K` -/

/-- The canonical inclusion `trunc j K ⟶ trunc (j-1) K`, the identity on the common terms. -/
def truncIncl (K : Cpx) (j : ℤ) : trunc j K ⟶ trunc (j - 1) K where
  f n := if h : j ≤ n then
      eqToHom (trunc_X_of_le K j h) ≫
        eqToHom (trunc_X_of_le K (j - 1) (le_trans (trunc_pred_le j) h)).symm
    else 0
  comm' i n hin := by
    rw [ComplexShape.up_Rel] at hin
    obtain rfl : n = i + 1 := by omega
    by_cases h : j ≤ i
    · have h1 : j ≤ i + 1 := by omega
      rw [dif_pos h, dif_pos h1]
      rw [trunc_d_eq K (m := j - 1) (i := i) (n := i + 1) rfl
            (le_trans (trunc_pred_le j) h) (le_trans (trunc_pred_le j) h1),
          trunc_d_eq K (m := j) (i := i) (n := i + 1) rfl h h1]
      simp only [Category.assoc, eqToHom_comp_eqToHom_self,
        eqToHom_comp_eqToHom_self_sandwich, Category.id_comp, Category.comp_id]
    · rw [dif_neg h, trunc_d_eq_zero K (m := j) (i := i) (n := i + 1) rfl h, zero_comp,
        zero_comp]

lemma truncIncl_f_of_le (K : Cpx) (j : ℤ) {n : ℤ} (h : j ≤ n) :
    (truncIncl K j).f n = eqToHom (trunc_X_of_le K j h) ≫
      eqToHom (trunc_X_of_le K (j - 1) (le_trans (trunc_pred_le j) h)).symm := by
  simp only [truncIncl, dif_pos h]

lemma truncIncl_f_of_not_le (K : Cpx) (j : ℤ) {n : ℤ} (h : ¬ j ≤ n) :
    (truncIncl K j).f n = 0 := by
  simp only [truncIncl, dif_neg h]

lemma isIso_truncIncl_f (K : Cpx) (j : ℤ) {n : ℤ} (h : j ≤ n) :
    IsIso ((truncIncl K j).f n) := by
  rw [truncIncl_f_of_le K j h]
  infer_instance

/-! ## The projection `trunc (j-1) K ⟶ single (j-1) (K.X (j-1))` -/

/-- The canonical projection onto the new term in degree `j-1`. -/
def truncProj (K : Cpx) (j : ℤ) :
    trunc (j - 1) K ⟶
      (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) (j - 1)).obj (K.X (j - 1)) where
  f n := if h : n = j - 1 then
      eqToHom (by
        subst h
        exact (trunc_X_of_le K (j - 1) le_rfl).trans
          (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) (j - 1)
            (K.X (j - 1))).symm)
    else 0
  comm' i n hin := by
    rw [ComplexShape.up_Rel] at hin
    obtain rfl : n = i + 1 := by omega
    rw [HomologicalComplex.single_obj_d, comp_zero]
    by_cases hn : i + 1 = j - 1
    · rw [trunc_d_eq_zero K (m := j - 1) (i := i) (n := i + 1) rfl (by omega), zero_comp]
    · rw [dif_neg hn, comp_zero]

lemma truncProj_f_of_ne (K : Cpx) (j : ℤ) {n : ℤ} (h : n ≠ j - 1) :
    (truncProj K j).f n = 0 := by
  simp only [truncProj, dif_neg h]

lemma truncProj_f_eq (K : Cpx) (j : ℤ) {n : ℤ} (h : n = j - 1) :
    (truncProj K j).f n =
      eqToHom (by
        subst h
        exact (trunc_X_of_le K (j - 1) le_rfl).trans
          (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) (j - 1)
            (K.X (j - 1))).symm) := by
  simp only [truncProj, dif_pos h]

lemma isIso_truncProj_f (K : Cpx) (j : ℤ) {n : ℤ} (h : n = j - 1) :
    IsIso ((truncProj K j).f n) := by
  rw [truncProj_f_eq K j h]
  infer_instance

lemma isZero_single_X (K : Cpx) (j : ℤ) {n : ℤ} (h : n ≠ j - 1) :
    IsZero (((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) (j - 1)).obj
      (K.X (j - 1))).X n) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (j - 1) (K.X (j - 1)) n h

lemma truncIncl_comp_truncProj (K : Cpx) (j : ℤ) : truncIncl K j ≫ truncProj K j = 0 := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f, truncIncl_f_of_not_le K j (by omega),
    zero_comp]

/-! ## The degreewise split short exact sequence -/

/-- The short complex `0 ⟶ trunc j K ⟶ trunc (j-1) K ⟶ single (j-1) (K.X (j-1)) ⟶ 0`. -/
def truncShortComplex (K : Cpx) (j : ℤ) : ShortComplex Cpx :=
  ShortComplex.mk (truncIncl K j) (truncProj K j) (truncIncl_comp_truncProj K j)

/-- The degreewise splitting of `truncShortComplex K j`. -/
noncomputable def truncSplitting (K : Cpx) (j : ℤ) (n : ℤ) :
    ((truncShortComplex K j).map
      (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) n)).Splitting := by
  by_cases h : j ≤ n
  · exact ShortComplex.Splitting.ofIsIsoOfIsZero (S := (truncShortComplex K j).map
        (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) n))
      (isIso_truncIncl_f K j h) (isZero_single_X K j (n := n) (by omega))
  · by_cases h2 : n = j - 1
    · exact ShortComplex.Splitting.ofIsZeroOfIsIso (S := (truncShortComplex K j).map
          (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) n))
        (isZero_trunc_X K j (n := n) (by omega)) (isIso_truncProj_f K j h2)
    · exact ShortComplex.Splitting.ofIsZero (S := (truncShortComplex K j).map
          (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) n))
        (isZero_trunc_X K j (n := n) (by omega))
        (isZero_trunc_X K (j - 1) (n := n) (by omega))
        (isZero_single_X K j (n := n) (by omega))

/-! ## The distinguished triangle -/

/-- The distinguished triangle of `K(LightCondAb)` with objects
`(single (j-1) (K.X (j-1)))⟦-1⟧`, `trunc j K` and `trunc (j-1) K`. -/
noncomputable def truncTriangle (K : Cpx) (j : ℤ) :
    CategoryTheory.Pretriangulated.Triangle KCat :=
  (CochainComplex.trianglehOfDegreewiseSplit (truncShortComplex K j)
    (truncSplitting K j)).invRotate

lemma truncTriangle_distinguished (K : Cpx) (j : ℤ) :
    truncTriangle K j ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
  HomotopyCategory.Pretriangulated.invRotate_distinguished_triangle' _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _)

lemma truncTriangle_obj₁ (K : Cpx) (j : ℤ) :
    (truncTriangle K j).obj₁ =
      (CategoryTheory.shiftFunctor KCat (-1)).obj
        (Submission.Blueprint.hq ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ)
          (j - 1)).obj (K.X (j - 1)))) := by
  rw [truncTriangle, CategoryTheory.Pretriangulated.Triangle.invRotate_obj₁]
  rfl

lemma truncTriangle_obj₂ (K : Cpx) (j : ℤ) :
    (truncTriangle K j).obj₂ = Submission.Blueprint.hq (trunc j K) := by
  rw [truncTriangle, CategoryTheory.Pretriangulated.Triangle.invRotate_obj₂]
  rfl

lemma truncTriangle_obj₃ (K : Cpx) (j : ℤ) :
    (truncTriangle K j).obj₃ = Submission.Blueprint.hq (trunc (j - 1) K) := by
  rw [truncTriangle, CategoryTheory.Pretriangulated.Triangle.invRotate_obj₃]
  rfl

/-! ## The main theorem -/

theorem solidCofibrant_trunc (hA : Submission.Blueprint.AtomProp)
    (hC : Work.RESOL.CofibrantClosure) (K : Work.RESOL.Cpx)
    (hat : Work.RESOL.HasAtomicTerms K) (j : ℤ)
    (h : Submission.Blueprint.SolidCofibrant (Work.RESOL.trunc j K)) :
    Submission.Blueprint.SolidCofibrant (Work.RESOL.trunc (j - 1) K) := by
  have hsingle : Submission.Blueprint.SolidCofibrant
      ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) (j - 1)).obj (K.X (j - 1))) :=
    solidCofibrant_single_atomic hA hC (K.X (j - 1)) (hat (j - 1)) (j - 1)
  have h1 : ∀ n : ℤ,
      SolidCofibrantH ((CategoryTheory.shiftFunctor KCat n).obj (truncTriangle K j).obj₁) := by
    intro n
    rw [truncTriangle_obj₁]
    exact hC.shift n _ (hC.shift (-1) _ hsingle)
  have h2 : ∀ n : ℤ,
      SolidCofibrantH ((CategoryTheory.shiftFunctor KCat n).obj (truncTriangle K j).obj₂) := by
    intro n
    rw [truncTriangle_obj₂]
    exact hC.shift n _ h
  have hZ : SolidCofibrantH (truncTriangle K j).obj₃ :=
    hC.cone (truncTriangle K j) (truncTriangle_distinguished K j) h1 h2
  rw [truncTriangle_obj₃] at hZ
  exact hZ

end Work.RESOL
