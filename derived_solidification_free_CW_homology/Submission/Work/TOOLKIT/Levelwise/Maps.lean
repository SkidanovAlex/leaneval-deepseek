/-
AREA TOOLKIT/Levelwise — the canonical chain maps attached to the brutal truncation:
functoriality `truncMap`, the inclusions `truncIncl` (between truncations) and `truncIntoK`
(into the ambient complex), and the projection `truncProj` onto the top term.
-/
import Submission.Work.TOOLKIT.Levelwise.Basic

open CategoryTheory Limits
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Work.TOOLKIT.Levelwise

variable {K L M : Cpx}

attribute [local simp] CategoryTheory.eqToHom_trans

/-! ## Elementary `eqToHom` lemmas -/

@[simp]
lemma eqToHom_comp_symm {X Y : Cpx} (p : X = Y) : eqToHom p ≫ eqToHom p.symm = 𝟙 X := by
  subst p
  simp

@[simp]
lemma eqToHom_symm_comp {X Y : Cpx} (p : X = Y) : eqToHom p.symm ≫ eqToHom p = 𝟙 Y := by
  subst p
  simp

/-- Sandwich form (right-associated) of `Iso.hom_inv_id`. -/
@[simp]
lemma iso_hom_inv_sandwich {X Y Z : Cpx} (e : X ≅ Y) (f : X ⟶ Z) :
    e.hom ≫ (e.inv ≫ f) = f := by
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Sandwich form (right-associated) of `Iso.inv_hom_id`. -/
@[simp]
lemma iso_inv_hom_sandwich {X Y Z : Cpx} (e : X ≅ Y) (f : Y ⟶ Z) :
    e.inv ≫ (e.hom ≫ f) = f := by
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- `Hom.comm` in the right-associated "sandwich" form. -/
lemma hom_comm_sandwich {K L : Cpx} (φ : K ⟶ L) (i : ℤ) {C : LightCondAb}
    (f : L.X (i + 1) ⟶ C) :
    φ.f i ≫ (L.d i (i + 1) ≫ f) = K.d i (i + 1) ≫ (φ.f (i + 1) ≫ f) := by
  rw [← Category.assoc, HomologicalComplex.Hom.comm φ i (i + 1), Category.assoc]

/-! ## Functoriality of the truncation in the complex -/

/-- `trunc j` is functorial: the map `trunc j K ⟶ trunc j L` induced by `φ : K ⟶ L`. -/
noncomputable def truncMap (φ : K ⟶ L) (j : ℤ) : trunc j K ⟶ trunc j L where
  f n := if h : j ≤ n then
      eqToHom (trunc_X_of_le h K) ≫ φ.f n ≫ eqToHom ((trunc_X_of_le h L).symm)
    else 0
  comm' i n hin := by
    rw [ComplexShape.up_Rel] at hin
    obtain rfl : n = i + 1 := by omega
    by_cases h : j ≤ i
    · have h2 : j ≤ i + 1 := by omega
      rw [dite_eq_left h, dite_eq_left h2, trunc_d_eq h h2 L, trunc_d_eq h h2 K]
      simp [hom_comm_sandwich φ i]
    · rw [dite_eq_right h, zero_comp, trunc_d_of_not_le h K, zero_comp]

@[simp]
lemma truncMap_f_of_le (φ : K ⟶ L) (j : ℤ) {n : ℤ} (h : j ≤ n) :
    (truncMap φ j).f n =
      eqToHom (trunc_X_of_le h K) ≫ φ.f n ≫ eqToHom ((trunc_X_of_le h L).symm) :=
  dite_eq_left h

@[simp]
lemma truncMap_f_of_not_le (φ : K ⟶ L) (j : ℤ) {n : ℤ} (h : ¬ j ≤ n) :
    (truncMap φ j).f n = 0 :=
  dite_eq_right h

@[simp]
lemma truncMap_id (j : ℤ) (K : Cpx) : truncMap (𝟙 K) j = 𝟙 (trunc j K) := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases h : j ≤ n
  · rw [truncMap_f_of_le (𝟙 K) j h, HomologicalComplex.id_f]
    simp
  · rw [truncMap_f_of_not_le (𝟙 K) j h, HomologicalComplex.id_f]
    exact (trunc_isZero_X h K).eq_of_src _ _

@[simp]
lemma truncMap_comp (φ : K ⟶ L) (ψ : L ⟶ M) (j : ℤ) :
    truncMap (φ ≫ ψ) j = truncMap φ j ≫ truncMap ψ j := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases h : j ≤ n
  · rw [HomologicalComplex.comp_f, truncMap_f_of_le (φ ≫ ψ) j h, truncMap_f_of_le φ j h,
      truncMap_f_of_le ψ j h]
    simp
  · rw [HomologicalComplex.comp_f, truncMap_f_of_not_le (φ ≫ ψ) j h,
      truncMap_f_of_not_le φ j h, truncMap_f_of_not_le ψ j h]
    simp

/-! ## The inclusion `trunc b K ⟶ trunc a K` (for `a ≤ b`) -/

/-- The inclusion of truncations `trunc b K ⟶ trunc a K` when `a ≤ b`. -/
noncomputable def truncIncl {a b : ℤ} (h : a ≤ b) (K : Cpx) : trunc b K ⟶ trunc a K where
  f n := if hb : b ≤ n then
      eqToHom (trunc_X_of_le hb K) ≫ eqToHom ((trunc_X_of_le (le_trans h hb) K).symm)
    else 0
  comm' i n hin := by
    rw [ComplexShape.up_Rel] at hin
    obtain rfl : n = i + 1 := by omega
    by_cases hb : b ≤ i
    · have hb2 : b ≤ i + 1 := by omega
      have ha : a ≤ i := le_trans h hb
      rw [dite_eq_left hb, dite_eq_left hb2, trunc_d_eq (le_trans h hb) (by omega) K,
        trunc_d_eq hb hb2 K]
      simp
    · rw [dite_eq_right hb, zero_comp, trunc_d_of_not_le hb K, zero_comp]

@[simp]
lemma truncIncl_f_of_le {a b n : ℤ} (h : a ≤ b) (hb : b ≤ n) (K : Cpx) :
    (truncIncl h K).f n =
      eqToHom (trunc_X_of_le hb K) ≫ eqToHom ((trunc_X_of_le (le_trans h hb) K).symm) :=
  dite_eq_left hb

@[simp]
lemma truncIncl_f_of_not_le {a b n : ℤ} (h : a ≤ b) (hb : ¬ b ≤ n) (K : Cpx) :
    (truncIncl h K).f n = 0 :=
  dite_eq_right hb

@[simp]
lemma truncIncl_self (a : ℤ) (K : Cpx) : truncIncl (le_refl a) K = 𝟙 (trunc a K) := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases h : a ≤ n
  · rw [truncIncl_f_of_le (le_refl a) h K]
    simp
  · rw [truncIncl_f_of_not_le (le_refl a) h K, HomologicalComplex.id_f]
    exact (trunc_isZero_X h K).eq_of_src _ _

/-- Transitivity of the inclusions of truncations. -/
@[simp]
lemma truncIncl_comp {a b c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) (K : Cpx) :
    truncIncl h₂ K ≫ truncIncl h₁ K = truncIncl (le_trans h₁ h₂) K := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hc : c ≤ n
  · have hb : b ≤ n := le_trans h₂ hc
    rw [HomologicalComplex.comp_f, truncIncl_f_of_le (le_trans h₁ h₂) hc K,
      truncIncl_f_of_le h₂ hc K, truncIncl_f_of_le h₁ hb K]
    simp
  · rw [HomologicalComplex.comp_f, truncIncl_f_of_not_le (le_trans h₁ h₂) hc K,
      truncIncl_f_of_not_le h₂ hc K, zero_comp]

/-- Naturality of the inclusion of truncations in the complex. -/
lemma truncIncl_naturality {a b : ℤ} (h : a ≤ b) (φ : K ⟶ L) :
    truncMap φ b ≫ truncIncl h L = truncIncl h K ≫ truncMap φ a := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hb : b ≤ n
  · have ha : a ≤ n := le_trans h hb
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, truncMap_f_of_le φ b hb,
      truncIncl_f_of_le h hb L, truncIncl_f_of_le h hb K, truncMap_f_of_le φ a ha]
    simp
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, truncMap_f_of_not_le φ b hb,
      truncIncl_f_of_not_le h hb L, truncIncl_f_of_not_le h hb K]
    by_cases ha : a ≤ n
    · rw [truncMap_f_of_le φ a ha]
      simp
    · rw [truncMap_f_of_not_le φ a ha]
      simp

/-! ## The inclusion `trunc j K ⟶ K` -/

/-- The inclusion of the truncation `trunc j K` into `K`. -/
noncomputable def truncIntoK (j : ℤ) (K : Cpx) : trunc j K ⟶ K where
  f n := if h : j ≤ n then eqToHom (trunc_X_of_le h K) else 0
  comm' i n hin := by
    rw [ComplexShape.up_Rel] at hin
    obtain rfl : n = i + 1 := by omega
    by_cases h : j ≤ i
    · have h2 : j ≤ i + 1 := by omega
      rw [dite_eq_left h, dite_eq_left h2, trunc_d_eq h h2 K]
      simp
    · rw [dite_eq_right h, zero_comp, trunc_d_of_not_le h K, zero_comp]

@[simp]
lemma truncIntoK_f_of_le {j n : ℤ} (h : j ≤ n) (K : Cpx) :
    (truncIntoK j K).f n = eqToHom (trunc_X_of_le h K) :=
  dite_eq_left h

@[simp]
lemma truncIntoK_f_of_not_le {j n : ℤ} (h : ¬ j ≤ n) (K : Cpx) :
    (truncIntoK j K).f n = 0 :=
  dite_eq_right h

/-- Naturality in the complex of the inclusion into `K`. -/
lemma truncMap_comp_truncIntoK (φ : K ⟶ L) (j : ℤ) :
    truncMap φ j ≫ truncIntoK j L = truncIntoK j K ≫ φ := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases h : j ≤ n
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, truncMap_f_of_le φ j h,
      truncIntoK_f_of_le h L, truncIntoK_f_of_le h K]
    simp
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, truncMap_f_of_not_le φ j h,
      truncIntoK_f_of_not_le h L, truncIntoK_f_of_not_le h K]
    simp

/-- The two inclusions are compatible. -/
lemma truncIncl_comp_truncIntoK {a b : ℤ} (h : a ≤ b) (K : Cpx) :
    truncIncl h K ≫ truncIntoK a K = truncIntoK b K := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hb : b ≤ n
  · rw [HomologicalComplex.comp_f, truncIncl_f_of_le h hb K,
      truncIntoK_f_of_le (le_trans h hb) K, truncIntoK_f_of_le hb K]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
      Category.comp_id, eqToHom_comp_symm, eqToHom_symm_comp, eqToHom_symm_comp_sandwich,
      eqToHom_comp_symm_sandwich]
  · rw [HomologicalComplex.comp_f, truncIncl_f_of_not_le h hb K, truncIntoK_f_of_not_le hb K,
      zero_comp]

/-! ## The projection onto the top term -/

/-- The projection `trunc j K ⟶ (sng j).obj (K.X j)` (the identity in degree `j`). -/
noncomputable def truncProj (K : Cpx) (j : ℤ) : trunc j K ⟶ (sng j).obj (K.X j) :=
  HomologicalComplex.mkHomToSingle (eqToHom (trunc_X_of_le (le_refl j) K))
    (fun i hi => by
      rw [ComplexShape.up_Rel] at hi
      obtain rfl : j = i + 1 := by omega
      rw [trunc_d_of_not_le (by omega) K, zero_comp])

@[simp]
lemma truncProj_f_self (K : Cpx) (j : ℤ) :
    (truncProj K j).f j = eqToHom (trunc_X_of_le (le_refl j) K) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j (K.X j)).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

@[simp]
lemma truncProj_f_of_ne (K : Cpx) (j : ℤ) {n : ℤ} (h : n ≠ j) : (truncProj K j).f n = 0 := by
  dsimp [truncProj, HomologicalComplex.mkHomToSingle]
  rw [dite_eq_right h]

/-- Naturality in the complex of the projection onto the top term. -/
lemma truncProj_naturality (φ : K ⟶ L) (j : ℤ) :
    truncMap φ j ≫ truncProj L j = truncProj K j ≫ (sng j).map (φ.f j) := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases h : n = j
  · subst n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      truncMap_f_of_le φ j (le_refl j), truncProj_f_self L j, truncProj_f_self K j,
      HomologicalComplex.single_map_f_self]
    simp
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    exact (isZero_sng_obj_X h (L.X j)).eq_of_tgt _ _

/-- The composite of the two maps of the truncation short complex vanishes. -/
lemma truncIncl_comp_truncProj {a b : ℤ} (h : a < b) (K : Cpx) :
    truncIncl (le_of_lt h) K ≫ truncProj K a = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = a
  · subst n
    rw [HomologicalComplex.comp_f, truncIncl_f_of_not_le (le_of_lt h) (by omega) K,
      zero_comp, HomologicalComplex.zero_f]
  · rw [HomologicalComplex.comp_f, truncProj_f_of_ne K a hn, HomologicalComplex.zero_f,
      comp_zero]

end Work.TOOLKIT.Levelwise
