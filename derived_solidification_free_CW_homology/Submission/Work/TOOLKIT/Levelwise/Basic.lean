/-
AREA TOOLKIT/Levelwise — the degreewise criterion for solid-equivalences (foundations).

This file sets up the vocabulary for the proof of `Work.TOOLKIT.Levelwise.solidEquiv_levelwise_of`:
the single complexes `sng q M` (the object `M` in degree `q`), the *brutal* truncation
`trunc j K` (the subcomplex of `trunc j K` given by the terms of `K` in degrees `≥ j`), and
degreewise lemmas about them.
-/
import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances

open CategoryTheory Limits
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.TOOLKIT.Levelwise

/-- The zero object of `LightCondAb`, as a `Zero` instance (the one provided by
`HasZeroObject` is not registered for this abbreviation).  Needed for the notation `0`. -/
instance instZeroLightCondAb : Zero LightCondAb := HasZeroObject.zero' LightCondAb

/-- The single complex of light condensed abelian groups with `M` in degree `q`. -/
abbrev sng (q : ℤ) : LightCondAb ⥤ Cpx :=
  HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) q

@[simp]
lemma sng_obj_X (q n : ℤ) (M : LightCondAb) : ((sng q).obj M).X n = if n = q then M else 0 := rfl

lemma sng_obj_X_self (q : ℤ) (M : LightCondAb) : ((sng q).obj M).X q = M :=
  HomologicalComplex.single_obj_X_self _ _ _

lemma isZero_sng_obj_X {q n : ℤ} (h : n ≠ q) (M : LightCondAb) :
    IsZero (((sng q).obj M).X n) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simpa [eq_comm] using h)

@[simp]
lemma sng_obj_d (q : ℤ) (M : LightCondAb) (i j : ℤ) : ((sng q).obj M).d i j = 0 := rfl

/-! ## The brutal truncation -/

variable (j : ℤ) (K : Cpx) in
/-- The *brutal truncation* `σ^{≥j}K`: same terms as `K` in degrees `≥ j`, zero below.
Marked `@[reducible]` so that the degreewise formulas are visible to unification at any
transparency (`trunc j K).X n = if j ≤ n then K.X n else 0`). -/
@[reducible] def trunc : Cpx where
  X n := if j ≤ n then K.X n else 0
  d i n := if h : j ≤ i ∧ j ≤ n ∧ i + 1 = n then
      (eqToHom (if_pos h.1) ≫ K.d i n ≫ eqToHom (if_pos h.2.1).symm) else 0
  shape i n hn := by
    rw [dif_neg]
    rintro ⟨h1, h2, h3⟩
    exact hn (by rw [ComplexShape.up_Rel]; exact h3)
  d_comp_d' i n k hin hnk := by
    rw [ComplexShape.up_Rel] at hin hnk
    obtain rfl : n = i + 1 := by omega
    obtain rfl : k = i + 1 + 1 := by omega
    by_cases h : j ≤ i
    · rw [dif_pos (show j ≤ i ∧ j ≤ i + 1 ∧ i + 1 = i + 1 from ⟨h, by omega, rfl⟩),
        dif_pos (show j ≤ i + 1 ∧ j ≤ (i + 1) + 1 ∧ (i + 1) + 1 = (i + 1) + 1 from
          ⟨by omega, by omega, rfl⟩)]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Category.comp_id]
      rw [← Category.assoc (f := K.d i (i + 1)) (g := K.d (i + 1) ((i + 1) + 1)),
        K.d_comp_d i (i + 1) ((i + 1) + 1)]
      simp
    · rw [dif_neg (by rintro ⟨h1, _⟩; exact h h1), zero_comp]

/-! ## `eqToHom` calculus in the right-associated normal form

`simp [Category.assoc]` normalises composites to the right-associated form
`f ≫ (g ≫ h)`.  The two lemmas below are the versions of `eqToHom_trans` and of the
cancellation of an inverse pair of `eqToHom`s which are stated in that normal form. -/

/-- Merging two adjacent `eqToHom`s in the right-associated normal form. -/
@[simp]
lemma eqToHom_trans_sandwich {A B C D : Cpx} (p : A = B) (q : B = C) (f : C ⟶ D) :
    eqToHom p ≫ (eqToHom q ≫ f) = eqToHom (p.trans q) ≫ f := by
  rw [← Category.assoc, eqToHom_trans]

/-- Cancelling an inverse pair of adjacent `eqToHom`s in the right-associated normal form. -/
@[simp]
lemma eqToHom_comp_symm_sandwich {A B C : Cpx} (p q : A = B) (f : A ⟶ C) :
    eqToHom p ≫ (eqToHom q.symm ≫ f) = f := by
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- Cancelling an inverse pair of adjacent `eqToHom`s in the right-associated normal form
(other order). -/
@[simp]
lemma eqToHom_symm_comp_sandwich {A B C : Cpx} (p q : A = B) (f : B ⟶ C) :
    eqToHom p.symm ≫ (eqToHom q ≫ f) = f := by
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

@[simp]
lemma trunc_X_of_le {j n : ℤ} (h : j ≤ n) (K : Cpx) : (trunc j K).X n = K.X n := if_pos h

lemma trunc_isZero_X {j n : ℤ} (h : ¬ j ≤ n) (K : Cpx) : IsZero ((trunc j K).X n) := by
  rw [show (trunc j K).X n = (0 : LightCondAb) from if_neg h]
  exact isZero_zero _

@[simp]
lemma trunc_d_of_le {j i : ℤ} (h : j ≤ i) (K : Cpx) :
    (trunc j K).d i (i + 1) =
      eqToHom (if_pos h) ≫ K.d i (i + 1) ≫ eqToHom (if_pos (by omega)).symm :=
  dif_pos ⟨h, by omega, rfl⟩

@[simp]
lemma trunc_d_of_not_le {j i : ℤ} (h : ¬ j ≤ i) (K : Cpx) : (trunc j K).d i (i + 1) = 0 :=
  dif_neg (by rintro ⟨h1, _, _⟩; exact h h1)

/-- The differential of the truncation, written with the *canonical* isomorphisms
`trunc_X_of_le` (the form in which the chain maps of `Levelwise/Maps.lean` are written, so
that the `eqToHom`s cancel syntactically). -/
lemma trunc_d_eq {j i : ℤ} (h1 : j ≤ i) (h2 : j ≤ i + 1) (K : Cpx) :
    (trunc j K).d i (i + 1) =
      eqToHom (trunc_X_of_le h1 K) ≫ K.d i (i + 1) ≫
        eqToHom ((trunc_X_of_le h2 K).symm) := by
  rw [trunc_d_of_le h1 K]

end Work.TOOLKIT.Levelwise
