/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : the point stabilizers in `PSL(2,F)`

* `Work.AUTL2.element_fixing_infty`: an element of `pslImage F` fixing `∞` is affine
  `x ↦ a²x + b` (this is the Borel subgroup of `PSL(2,F)`);
* `Work.AUTL2.fixing_infty_zero`: an element of `pslImage F` fixing `∞` and `0` is a dilation
  `x ↦ a²x`;
* `Work.AUTL2.exists_pslImage_map_to_infty`: `pslImage F` is transitive on `ℙ¹(F)`.
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]

/-- An element of `pslImage F` fixing `∞` is affine, `x ↦ a²x + b`.
This is the Borel subgroup of `PSL(2,F)`; the multiplier is a square because `PSL` is
`SL/{±1}`. -/
lemma element_fixing_infty (g : Equiv.Perm (P1 F)) (hg : g ∈ pslImage F)
    (hinf : g (∞ : P1 F) = ∞) :
    ∃ (a : Fˣ) (b : F), ∀ x : F, g (x : P1 F) = ((↑a ^ 2 * x + b : F) : P1 F) := by
  obtain ⟨u, rfl⟩ := hg
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective u
  have h10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    by_contra hne
    have h := hinf
    rw [pslHom_toGL, OnePoint.smul_infty_eq_ite, coe_toGL_coe] at h
    rw [if_neg hne] at h
    exact OnePoint.coe_ne_infty _ h
  have hdet1 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h1 : Matrix.det (M : Matrix (Fin 2) (Fin 2) F) = 1 := M.2
    rwa [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h1
  have h00 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h; rw [h, zero_mul] at hdet1; exact absurd hdet1 (by simp)
  have h11 : (M : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h; rw [h, mul_zero] at hdet1; exact absurd hdet1 (by simp)
  refine ⟨⟨(M : Matrix (Fin 2) (Fin 2) F) 0 0, (M : Matrix (Fin 2) (Fin 2) F) 1 1, hdet1,
    by rw [mul_comm]; exact hdet1⟩, (M : Matrix (Fin 2) (Fin 2) F) 0 0 *
      (M : Matrix (Fin 2) (Fin 2) F) 0 1, fun x => ?_⟩
  rw [pslHom_toGL, OnePoint.smul_some_eq_ite, coe_toGL_coe, h10, zero_mul, zero_add, if_neg h11]
  congr 1
  rw [div_eq_iff h11]
  linear_combination -(((M : Matrix (Fin 2) (Fin 2) F) 0 0 * x +
    (M : Matrix (Fin 2) (Fin 2) F) 0 1) * hdet1)

/-- An element of `pslImage F` fixing `∞` and `0` is a dilation `x ↦ a²x`. -/
lemma fixing_infty_zero (g : Equiv.Perm (P1 F)) (hg : g ∈ pslImage F)
    (hinf : g (∞ : P1 F) = ∞) (h0 : g ((0 : F) : P1 F) = ((0 : F) : P1 F)) :
    ∃ a : Fˣ, ∀ x : F, g (x : P1 F) = ((↑a ^ 2 * x : F) : P1 F) := by
  obtain ⟨a, b, h⟩ := element_fixing_infty F g hg hinf
  have hb : b = 0 := by
    have h0' := h 0
    rw [h0] at h0'
    simpa using (OnePoint.coe_eq_coe.1 h0'.symm)
  exact ⟨a, fun x => by rw [h x, hb, add_zero]⟩

/-- `pslImage F` is transitive on `ℙ¹(F)`: every point is moved to `∞` (by
`weylEl * transl (-c)`, i.e. `x ↦ -1/(x - c)`). -/
lemma exists_pslImage_map_to_infty (y : P1 F) :
    ∃ g : Equiv.Perm (P1 F), g ∈ pslImage F ∧ g y = ∞ := by
  rcases y with _ | c
  · exact ⟨1, Subgroup.one_mem _, rfl⟩
  · refine ⟨weylEl F * transl F (-c), ?_, ?_⟩
    · exact mul_mem (weylEl_mem F) (transl_mem F (-c))
    · change (weylEl F * transl F (-c)) (c : P1 F) = ∞
      rw [Equiv.Perm.mul_apply, transl_formula, add_neg_cancel]
      exact weyl_zero F

end Work.AUTL2
