/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : the Möbius action of `PSL(2,F)` on `ℙ¹(F)`

Computational layer of the area `Submission/Work/AUTL2/`:

* `Work.AUTL2.transl`: `x ↦ x + b`, `∞ ↦ ∞`, an element of `pslImage F`;
* `Work.AUTL2.dil`: `x ↦ a²x`, `∞ ↦ ∞`, an element of `pslImage F`;
* `Work.AUTL2.weylEl`: `x ↦ -1/x`, an element of `pslImage F`;
* `element_fixing_infty`: an element of `pslImage F` fixing `∞` is affine `x ↦ a²x + b`
  (the Borel subgroup of `PSL(2,F)`);
* `perm_three_transitive`: `PGL(2,F)` is 3-transitive on `ℙ¹(F)`.
-/
import Mathlib
import Submission.Work.AUTL2.Defs

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]

/-- Coercion `SL(2,F) → GL(2,F) → Matrix (Fin 2) (Fin 2) F` is the identity. -/
@[simp] lemma coe_toGL_coe (g : SL(2, F)) :
    ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) := rfl

/-- The entries of the matrices used below, in a form `simp` can consume. -/
private lemma unipotent_entry (b : F) :
    ((unipotentMat F b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1] := rfl
private lemma diag_entry (a : Fˣ) :
    ((diagMat F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![↑a, 0; 0, ↑a⁻¹] := rfl
private lemma weyl_entry :
    ((weylMat F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

/-- `transl b` is the translation `x ↦ x + b`. -/
lemma transl_formula (b x : F) : transl F b (x : P1 F) = ((x + b : F) : P1 F) := by
  rw [transl, pslHom_toGL, OnePoint.smul_some_eq_ite, coe_toGL_coe, unipotent_entry]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply]
  simp

lemma transl_infty (b : F) : transl F b (∞ : P1 F) = ∞ := by
  rw [transl, pslHom_toGL, OnePoint.smul_infty_eq_ite, coe_toGL_coe, unipotent_entry]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply]
  simp

lemma transl_zero : transl F 0 = 1 := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => by rw [transl_formula]; simp⟩
  rw [transl_infty]
  exact Equiv.Perm.one_apply _

lemma transl_mul (b c : F) : transl F b * transl F c = transl F (c + b) := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · rw [Equiv.Perm.mul_apply, transl_infty, transl_infty, transl_infty]
  · rw [Equiv.Perm.mul_apply, transl_formula, transl_formula, transl_formula]
    simp [add_assoc, add_comm, add_left_comm]

lemma transl_fixed (b : F) (hb : b ≠ 0) : ∀ x : P1 F, transl F b x = x → x = ∞ := by
  rw [OnePoint.forall]
  refine ⟨fun _ => rfl, fun y hy => ?_⟩
  exfalso
  have h : ((y + b : F) : P1 F) = (y : P1 F) := by
    rw [← transl_formula F b y]; exact hy
  rw [OnePoint.some_eq_iff] at h
  have h2 : y + b = y + 0 := by simpa using h
  exact hb (add_left_cancel h2)

/-- The five facts about the translations. -/
theorem transl_facts (F : Type*) [Field F] [DecidableEq F] :
    (∀ b x : F, transl F b (x : P1 F) = ((x + b : F) : P1 F)) ∧
    (∀ b : F, transl F b (∞ : P1 F) = ∞) ∧
    (transl F 0 = 1) ∧
    (∀ b c : F, transl F b * transl F c = transl F (b + c)) ∧
    (∀ b : F, b ≠ 0 → ∀ x : P1 F, transl F b x = x → x = ∞) :=
  ⟨fun b x => transl_formula F b x, fun b => transl_infty F b, transl_zero F,
    fun b c => by rw [transl_mul, add_comm],
    fun b hb x hx => transl_fixed F b hb x hx⟩

/-- `dil a` is `x ↦ a²x`. -/
lemma dil_formula (a : Fˣ) (x : F) : dil F a (x : P1 F) = ((↑a ^ 2 * x : F) : P1 F) := by
  rw [dil, pslHom_toGL, OnePoint.smul_some_eq_ite, coe_toGL_coe, diag_entry]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply]
  split_ifs with h
  · exact absurd h (by simpa using Units.ne_zero a⁻¹)
  · congr 1
    simp only [zero_mul, mul_zero, add_zero, zero_add]
    rw [div_eq_iff (Units.ne_zero a⁻¹), Units.val_inv_eq_inv_val, sq]
    field_simp
    try ring

lemma dil_infty (a : Fˣ) : dil F a (∞ : P1 F) = ∞ := by
  rw [dil, pslHom_toGL, OnePoint.smul_infty_eq_ite, coe_toGL_coe, diag_entry]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply]
  simp

lemma dil_mul' (a b : Fˣ) : dil F a * dil F b = dil F (b * a) := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · rw [Equiv.Perm.mul_apply, dil_infty, dil_infty, dil_infty]
  · rw [Equiv.Perm.mul_apply, dil_formula, dil_formula, dil_formula]
    simp only [Units.val_mul, OnePoint.some_eq_iff]
    ring

lemma dil_eq_one (a : Fˣ) (h : dil F a = 1) : a ^ 2 = 1 := by
  have h1 := congrFun (congrArg DFunLike.coe h) ((1 : F) : P1 F)
  rw [dil_formula] at h1
  simp only [Equiv.Perm.one_apply, OnePoint.some_eq_iff] at h1
  refine Units.ext ?_
  simpa using h1

/-- The four facts about the diagonal elements. -/
theorem dil_facts (F : Type*) [Field F] [DecidableEq F] :
    (∀ (a : Fˣ) (x : F), dil F a (x : P1 F) = ((↑a ^ 2 * x : F) : P1 F)) ∧
    (∀ a : Fˣ, dil F a (∞ : P1 F) = ∞) ∧
    (∀ a b : Fˣ, dil F a * dil F b = dil F (a * b)) ∧
    (∀ a : Fˣ, dil F a = 1 → a ^ 2 = 1) :=
  ⟨fun a x => dil_formula F a x, fun a => dil_infty F a,
    fun a b => by rw [dil_mul', mul_comm], fun a => dil_eq_one F a⟩

/-- `weylEl` is `x ↦ -1/x`. -/
lemma weyl_formula (x : F) (hx : x ≠ 0) : weylEl F (x : P1 F) = ((-x⁻¹ : F) : P1 F) := by
  rw [weylEl, pslHom_toGL, OnePoint.smul_some_eq_ite, coe_toGL_coe, weyl_entry]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply]
  split_ifs with h
  · exact absurd h (by simpa using hx)
  · congr 1
    simp only [zero_mul, one_mul, zero_add, add_zero, neg_mul]
    field_simp
    try ring

lemma weyl_infty : weylEl F (∞ : P1 F) = ((0 : F) : P1 F) := by
  rw [weylEl, pslHom_toGL, OnePoint.smul_infty_eq_ite, coe_toGL_coe, weyl_entry]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply]
  simp

lemma weyl_zero : weylEl F ((0 : F) : P1 F) = ∞ := by
  rw [weylEl, pslHom_toGL, OnePoint.smul_some_eq_ite, coe_toGL_coe, weyl_entry]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply]
  simp

lemma weyl_self : weylEl F * weylEl F = 1 := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · rw [Equiv.Perm.mul_apply, weyl_infty, weyl_zero]
    exact Equiv.Perm.one_apply _
  · rw [Equiv.Perm.mul_apply]
    rcases eq_or_ne x 0 with rfl | hx
    · rw [weyl_zero, weyl_infty]
      simp
    · rw [weyl_formula F x hx, weyl_formula F (-x⁻¹)]
      · simp
      · simpa using inv_ne_zero (neg_ne_zero.2 hx)

/-- The four facts about the Weyl element. -/
theorem weyl_facts (F : Type*) [Field F] [DecidableEq F] :
    (weylEl F (∞ : P1 F) = ((0 : F) : P1 F)) ∧
    (weylEl F ((0 : F) : P1 F) = ∞) ∧
    (∀ x : F, x ≠ 0 → weylEl F (x : P1 F) = ((-x⁻¹ : F) : P1 F)) ∧
    (weylEl F * weylEl F = 1) :=
  ⟨weyl_infty F, weyl_zero F, fun x hx => weyl_formula F x hx, weyl_self F⟩

end Work.AUTL2
