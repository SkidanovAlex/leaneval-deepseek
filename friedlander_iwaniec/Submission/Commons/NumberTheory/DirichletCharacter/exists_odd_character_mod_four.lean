import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.DedekindFinite
import Mathlib.NumberTheory.DirichletCharacter.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.DirichletCharacter

open Complex

/-- The underlying function of the nontrivial character modulo `4`: it sends `0 ↦ 0`,
`1 ↦ 1`, `2 ↦ 0` and `3 ↦ -1`. -/
noncomputable def chi4Fun (a : ZMod 4) : ℂ :=
  match a.val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | _ => -1

section ValLemmas

@[simp] lemma val_zero_four : (0 : ZMod 4).val = 0 := by decide
@[simp] lemma val_one_four : (1 : ZMod 4).val = 1 := by decide
@[simp] lemma val_two_four : (2 : ZMod 4).val = 2 := by decide
@[simp] lemma val_three_four : (3 : ZMod 4).val = 3 := by decide

end ValLemmas

/-- Every element of `ZMod 4` is one of `0, 1, 2, 3`. -/
lemma zmod_four_eq (a : ZMod 4) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
  have h : a.val < 4 := ZMod.val_lt a
  have h' : a = (a.val : ZMod 4) := (ZMod.natCast_zmod_val a).symm
  rw [h']
  interval_cases a.val
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; rfl

@[simp] lemma chi4Fun_zero : chi4Fun 0 = 0 := by simp [chi4Fun]
@[simp] lemma chi4Fun_one : chi4Fun 1 = 1 := by simp [chi4Fun]
@[simp] lemma chi4Fun_two : chi4Fun 2 = 0 := by simp [chi4Fun]
@[simp] lemma chi4Fun_three : chi4Fun 3 = -1 := by simp [chi4Fun]

lemma chi4Fun_map_mul (a b : ZMod 4) : chi4Fun (a * b) = chi4Fun a * chi4Fun b := by
  rcases zmod_four_eq a with rfl | rfl | rfl | rfl <;>
  rcases zmod_four_eq b with rfl | rfl | rfl | rfl <;>
  simp only [chi4Fun, ZMod.val_mul, val_zero_four, val_one_four, val_two_four,
    val_three_four] <;>
  norm_num

lemma chi4Fun_map_nonunit (a : ZMod 4) (ha : ¬ IsUnit a) : chi4Fun a = 0 := by
  rcases zmod_four_eq a with rfl | rfl | rfl | rfl
  · exact chi4Fun_zero
  · exact absurd isUnit_one ha
  · exact chi4Fun_two
  · exact absurd (isUnit_iff_exists_inv.mpr ⟨3, by decide⟩) ha

/-- The nontrivial Dirichlet character modulo `4` (`χ₄`). -/
noncomputable def chi4 : DirichletCharacter ℂ 4 :=
  MulChar.mk
    { toFun := chi4Fun
      map_one' := chi4Fun_one
      map_mul' := chi4Fun_map_mul }
    chi4Fun_map_nonunit

@[simp] lemma chi4_apply (a : ZMod 4) : chi4 a = chi4Fun a := rfl

theorem exists_odd_character_mod_four :
    ∃ χ : DirichletCharacter ℂ 4,
      χ 1 = 1 ∧ χ 2 = 0 ∧ χ 3 = -1 ∧ χ 0 = 0 ∧ ¬ χ.Even := by
  refine ⟨chi4, chi4Fun_one, chi4Fun_two, chi4Fun_three, chi4Fun_zero, ?_⟩
  intro h
  have h3 : chi4 (3 : ZMod 4) = 1 := by
    have hneg : (-1 : ZMod 4) = 3 := by decide
    have h1 : chi4 (-1) = 1 := h
    rwa [hneg] at h1
  rw [chi4_apply, chi4Fun_three] at h3
  norm_num at h3

end Commons.NumberTheory.DirichletCharacter