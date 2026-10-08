/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : `PGL(2,F)` is 3-transitive on `ℙ¹(F)`

* `Work.AUTL2.Mobius.perm_three_transitive`: `PGL(2,F)` acts 3-transitively on the projective
  line `ℙ¹(F) = OnePoint F`.

The proof reduces both ordered triples to the standard triple `(∞, 0, 1)`. Concretely we show
(`exists_gl_map_to_std`) that for any three distinct points `x, y, z` there is a matrix
`G ∈ GL(2,F)` whose Möbius action sends `x ↦ ∞`, `y ↦ 0` and `z ↦ 1`; this is proved by a short
case analysis on which of the three points (if any) is `∞`, with the corresponding matrix written
down explicitly. Given `G₁` for `(x,y,z)` and `G₂` for `(x',y',z')`, the element
`G₂⁻¹ * G₁ ∈ GL(2,F)` maps `x ↦ x'`, `y ↦ y'`, `z ↦ z'`, and its image in `PGL(2,F)` is the
required group element.
-/
import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Mobius

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Mobius

/-- The `GL(2,F)`-action agrees with the permutation induced by the class in `PGL(2,F)`. -/
private lemma pglHom_mk (F : Type*) [Field F] [DecidableEq F] (G : GL (Fin 2) F)
    (p : Work.AUTL2.P1 F) :
    Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk G) p = G • p := by
  rw [Work.AUTL2.pglHom, MulAction.toPermHom_apply, MulAction.toPerm_apply]
  simp only [Matrix.ProjGenLinGroup.mk_smul]

/-- Case `x, y, z` all finite. The matrix `!![λ, -λ b; 1, -a]` with `λ = (c-a)/(c-b)` realises
`a ↦ ∞`, `b ↦ 0`, `c ↦ 1`. -/
private lemma three_trans_case_finite (F : Type*) [Field F] [DecidableEq F]
    (a b c : F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ G : GL (Fin 2) F, G • ((a : F) : Work.AUTL2.P1 F) = (∞ : Work.AUTL2.P1 F) ∧
      G • ((b : F) : Work.AUTL2.P1 F) = ((0 : F) : Work.AUTL2.P1 F) ∧
      G • ((c : F) : Work.AUTL2.P1 F) = ((1 : F) : Work.AUTL2.P1 F) := by
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
  have hca : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hdet : (!![ (c - a) / (c - b), -((c - a) / (c - b)) * b; 1, -a] :
      Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    have h : (c - a) / (c - b) * -a - -((c - a) / (c - b)) * b * 1
        = ((c - a) / (c - b)) * (b - a) := by ring
    rw [h]
    exact mul_ne_zero (div_ne_zero hca hcb) hba
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(c - a) / (c - b), -((c - a) / (c - b)) * b; 1, -a] hdet, ?_, ?_, ?_⟩
  · rw [OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_left (by ring)]
  · rw [OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_right (by rw [← sub_eq_add_neg, one_mul]; exact hba)]
    refine congrArg _ ?_
    rw [div_eq_iff (by rw [← sub_eq_add_neg, one_mul]; exact hba)]
    ring
  · rw [OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_right (by rw [← sub_eq_add_neg, one_mul]; exact hca)]
    refine congrArg _ ?_
    rw [div_eq_iff (by rw [← sub_eq_add_neg, one_mul]; exact hca)]
    field_simp
    ring

/-- Case `x = ∞`: the affine matrix `!![1/(c-b), -b/(c-b); 0, 1]` fixes `∞` and sends `b ↦ 0`,
`c ↦ 1`. -/
private lemma three_trans_case_infty_first (F : Type*) [Field F] [DecidableEq F]
    (b c : F) (hbc : b ≠ c) :
    ∃ G : GL (Fin 2) F, G • (∞ : Work.AUTL2.P1 F) = (∞ : Work.AUTL2.P1 F) ∧
      G • ((b : F) : Work.AUTL2.P1 F) = ((0 : F) : Work.AUTL2.P1 F) ∧
      G • ((c : F) : Work.AUTL2.P1 F) = ((1 : F) : Work.AUTL2.P1 F) := by
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
  have hdet : (!![1 / (c - b), -(1 / (c - b)) * b; 0, 1] :
      Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [show 1 / (c - b) * 1 - -(1 / (c - b)) * b * 0 = 1 / (c - b) by ring]
    exact div_ne_zero one_ne_zero hcb
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1 / (c - b), -(1 / (c - b)) * b; 0, 1] hdet, ?_, ?_, ?_⟩
  · rw [OnePoint.smul_infty_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_left trivial]
  · rw [OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_right (by rw [zero_mul, zero_add]; exact one_ne_zero)]
    refine congrArg _ ?_
    rw [show 1 / (c - b) * b + -(1 / (c - b)) * b = 0 by ring]
    exact zero_div _
  · rw [OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_right (by rw [zero_mul, zero_add]; exact one_ne_zero)]
    refine congrArg _ ?_
    field_simp
    ring

/-- Case `y = ∞`: the matrix `!![0, c-a; 1, -a]` sends `a ↦ ∞`, `∞ ↦ 0` and `c ↦ 1`. -/
private lemma three_trans_case_infty_middle (F : Type*) [Field F] [DecidableEq F]
    (a c : F) (hac : a ≠ c) :
    ∃ G : GL (Fin 2) F, G • ((a : F) : Work.AUTL2.P1 F) = (∞ : Work.AUTL2.P1 F) ∧
      G • (∞ : Work.AUTL2.P1 F) = ((0 : F) : Work.AUTL2.P1 F) ∧
      G • ((c : F) : Work.AUTL2.P1 F) = ((1 : F) : Work.AUTL2.P1 F) := by
  have hca : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
  have hdet : (!![0, c - a; 1, -a] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [show (0 : F) * -a - (c - a) * 1 = -(c - a) by ring]
    exact neg_ne_zero.mpr hca
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, c - a; 1, -a] hdet, ?_, ?_, ?_⟩
  · rw [OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_left (by ring)]
  · rw [OnePoint.smul_infty_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_right one_ne_zero]
    norm_num
  · rw [OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_right (by rw [← sub_eq_add_neg, one_mul]; exact hca)]
    refine congrArg _ ?_
    rw [div_eq_iff (by rw [← sub_eq_add_neg, one_mul]; exact hca)]
    ring

/-- Case `z = ∞`: the matrix `!![1, -b; 1, -a]` sends `a ↦ ∞`, `b ↦ 0` and `∞ ↦ 1`. -/
private lemma three_trans_case_infty_last (F : Type*) [Field F] [DecidableEq F]
    (a b : F) (hab : a ≠ b) :
    ∃ G : GL (Fin 2) F, G • ((a : F) : Work.AUTL2.P1 F) = (∞ : Work.AUTL2.P1 F) ∧
      G • ((b : F) : Work.AUTL2.P1 F) = ((0 : F) : Work.AUTL2.P1 F) ∧
      G • (∞ : Work.AUTL2.P1 F) = ((1 : F) : Work.AUTL2.P1 F) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hdet : (!![1, -b; 1, -a] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [show (1 : F) * -a - (-b) * 1 = b - a by ring]
    exact hba
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, -b; 1, -a] hdet, ?_, ?_, ?_⟩
  · rw [OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_left (by ring)]
  · rw [OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_right (by rw [← sub_eq_add_neg, one_mul]; exact hba)]
    refine congrArg _ ?_
    rw [show (1 : F) * b + -b = 0 by ring]
    exact zero_div _
  · rw [OnePoint.smul_infty_eq_ite]
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [ite_eq_right one_ne_zero]
    norm_num

/-- For any three distinct points of `ℙ¹(F)` there is `G ∈ GL(2,F)` whose Möbius action sends them
to `∞`, `0`, `1` respectively. -/
private lemma exists_gl_map_to_std (F : Type*) [Field F] [DecidableEq F]
    (x y z : Work.AUTL2.P1 F) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ G : GL (Fin 2) F, G • x = (∞ : Work.AUTL2.P1 F) ∧
      G • y = ((0 : F) : Work.AUTL2.P1 F) ∧
      G • z = ((1 : F) : Work.AUTL2.P1 F) := by
  rcases x with _ | a
  · rcases y with _ | b
    · exact absurd rfl hxy
    · rcases z with _ | c
      · exact absurd rfl hxz
      · exact three_trans_case_infty_first F b c (fun h => hyz (by rw [h]))
  · rcases y with _ | b
    · rcases z with _ | c
      · exact absurd rfl hyz
      · exact three_trans_case_infty_middle F a c (fun h => hxz (by rw [h]))
    · rcases z with _ | c
      · exact three_trans_case_infty_last F a b (fun h => hxy (by rw [h]))
      · exact three_trans_case_finite F a b c (fun h => hxy (by rw [h]))
          (fun h => hxz (by rw [h])) (fun h => hyz (by rw [h]))

lemma perm_three_transitive (F : Type*) [Field F] [DecidableEq F]
    (x y z x' y' z' : Work.AUTL2.P1 F) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxy' : x' ≠ y') (hxz' : x' ≠ z') (hyz' : y' ≠ z') :
    ∃ g : Matrix.ProjGenLinGroup (Fin 2) F, Work.AUTL2.pglHom F g x = x' ∧
      Work.AUTL2.pglHom F g y = y' ∧ Work.AUTL2.pglHom F g z = z' := by
  obtain ⟨G₁, hx₁, hy₁, hz₁⟩ := exists_gl_map_to_std F x y z hxy hxz hyz
  obtain ⟨G₂, hx₂, hy₂, hz₂⟩ := exists_gl_map_to_std F x' y' z' hxy' hxz' hyz'
  have hx₂' : G₂⁻¹ • (∞ : Work.AUTL2.P1 F) = x' := by
    rw [← hx₂, ← mul_smul, inv_mul_cancel, one_smul]
  have hy₂' : G₂⁻¹ • ((0 : F) : Work.AUTL2.P1 F) = y' := by
    rw [← hy₂, ← mul_smul, inv_mul_cancel, one_smul]
  have hz₂' : G₂⁻¹ • ((1 : F) : Work.AUTL2.P1 F) = z' := by
    rw [← hz₂, ← mul_smul, inv_mul_cancel, one_smul]
  refine ⟨Matrix.ProjGenLinGroup.mk (G₂⁻¹ * G₁), ?_, ?_, ?_⟩
  · rw [pglHom_mk, mul_smul, hx₁]; exact hx₂'
  · rw [pglHom_mk, mul_smul, hy₁]; exact hy₂'
  · rw [pglHom_mk, mul_smul, hz₁]; exact hz₂'

end Work.AUTL2.Mobius
