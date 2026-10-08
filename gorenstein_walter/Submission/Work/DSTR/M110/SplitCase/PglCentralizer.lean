/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The centralizer of the split involution `x ↦ -x` in `PGL(2,F)`

For a field `F` of characteristic `≠ 2`:

* `pglImage_fixing_infty`: an element of `pglImage F` fixing `∞` is affine `x ↦ c·x + b`;
* `pglImage_fixing_zero_infty`: an element of `pglImage F` fixing both `0` and `∞` is diagonal,
  i.e. lies in the torus `torSub F = {x ↦ c·x}`;
* `pglImage_centralizer_negPerm`: an element of `pglImage F` commuting with the split involution
  `negPerm F` is diagonal (`∈ torSub F`) or anti-diagonal (`weylEl F * c ∈ torSub F`).
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.TorusConj

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110.SplitAux

open Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]

/-- An element of `pglImage F` fixing `∞` is affine, `x ↦ c·x + b` with `c ≠ 0`. -/
theorem pglImage_fixing_infty (g : Equiv.Perm (P1 F)) (hg : g ∈ pglImage F)
    (hinf : g (∞ : P1 F) = ∞) :
    ∃ (c b : F), c ≠ 0 ∧ ∀ x : F, g (x : P1 F) = ((c * x + b : F) : P1 F) := by
  obtain ⟨u, rfl⟩ := hg
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective u
  have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    by_contra hne
    have h := hinf
    rw [Galois.pglHom_mk_apply, OnePoint.smul_infty_eq_ite, if_neg hne] at h
    exact OnePoint.coe_ne_infty _ h
  have hdet : Matrix.det (A : Matrix (Fin 2) (Fin 2) F) ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h
    rw [Matrix.det_fin_two, h10, mul_zero, h, mul_zero, sub_zero] at hdet
    exact hdet rfl
  have h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    rw [Matrix.det_fin_two, h10, mul_zero, h, zero_mul, sub_zero] at hdet
    exact hdet rfl
  refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 0 / (A : Matrix (Fin 2) (Fin 2) F) 1 1,
    (A : Matrix (Fin 2) (Fin 2) F) 0 1 / (A : Matrix (Fin 2) (Fin 2) F) 1 1,
    div_ne_zero h00 h11, fun x => ?_⟩
  rw [Galois.pglHom_mk_apply, OnePoint.smul_some_eq_ite, h10, zero_mul, zero_add,
    if_neg h11]
  congr 1
  field_simp

/-- An element of `pglImage F` fixing `0` and `∞` is diagonal, and lies in `torSub F`. -/
theorem pglImage_fixing_zero_infty (g : Equiv.Perm (P1 F)) (hg : g ∈ pglImage F)
    (h0 : g ((0 : F) : P1 F) = ((0 : F) : P1 F)) (hinf : g (∞ : P1 F) = ∞) :
    g ∈ torSub F := by
  obtain ⟨c, b, hc, hg'⟩ := pglImage_fixing_infty F g hg hinf
  have hb : b = 0 := by
    have h := hg' 0
    rw [h0, mul_zero, zero_add] at h
    exact OnePoint.coe_eq_coe.mp h.symm
  have hge : g = smulHom F (Units.mk0 c hc) := by
    rw [Equiv.ext_iff, OnePoint.forall]
    refine ⟨hinf.trans (smulHom_apply_infty F _).symm, fun x => ?_⟩
    rw [hg' x, hb, add_zero, smulHom_apply_some, Units.val_mk0]
  rw [hge]
  exact ⟨Units.mk0 c hc, rfl⟩

/-- A point fixed by the split involution `x ↦ -x` is `0` or `∞` (characteristic `≠ 2`). -/
lemma eq_zero_or_eq_infty_of_negPerm_fixed (h2 : (2 : F) ≠ 0) {y : P1 F}
    (hy : negPerm F y = y) : y = ((0 : F) : P1 F) ∨ y = (∞ : P1 F) := by
  rcases y with _ | x
  · exact Or.inr rfl
  · left
    have h : ((-x : F) : P1 F) = ((x : F) : P1 F) := by
      rw [← negPerm_some F x]; exact hy
    have hx : -x = x := OnePoint.coe_eq_coe.mp h
    have hzero : x + x = 0 := by rw [← neg_eq_iff_add_eq_zero]; exact hx
    have : (2 : F) * x = 0 := by linear_combination hzero
    have hxz : x = 0 := by
      rcases mul_eq_zero.mp this with hh | hh
      · exact absurd hh h2
      · exact hh
    rw [hxz]
    rfl

/-- **The centralizer of the split involution in `PGL(2,F)`.**  An element of `pglImage F`
commuting with `x ↦ -x` is diagonal or anti-diagonal (characteristic `≠ 2`). -/
theorem pglImage_centralizer_negPerm (h2 : (2 : F) ≠ 0) (c : Equiv.Perm (P1 F))
    (hc : c ∈ pglImage F) (hcomm : c * negPerm F = negPerm F * c) :
    c ∈ torSub F ∨ weylEl F * c ∈ torSub F := by
  have hc0 : negPerm F (c ((0 : F) : P1 F)) = c ((0 : F) : P1 F) := by
    have h := congrFun (congrArg DFunLike.coe hcomm) ((0 : F) : P1 F)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, negPerm_some, neg_zero] at h
    exact h.symm
  have hcinf : negPerm F (c (∞ : P1 F)) = c (∞ : P1 F) := by
    have h := congrFun (congrArg DFunLike.coe hcomm) (∞ : P1 F)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, negPerm_infty] at h
    exact h.symm
  rcases eq_zero_or_eq_infty_of_negPerm_fixed F h2 hc0 with h | h
  · -- diagonal case
    left
    have hcinf' : c (∞ : P1 F) = ∞ := by
      rcases eq_zero_or_eq_infty_of_negPerm_fixed F h2 hcinf with h' | h'
      · exact absurd ((c.injective (h'.trans h.symm)).symm) (OnePoint.coe_ne_infty 0)
      · exact h'
    exact pglImage_fixing_zero_infty F c hc h hcinf'
  · -- anti-diagonal case
    right
    have hcinf' : c (∞ : P1 F) = ((0 : F) : P1 F) := by
      rcases eq_zero_or_eq_infty_of_negPerm_fixed F h2 hcinf with h' | h'
      · exact h'
      · exact absurd ((c.injective (h'.trans h.symm)).symm) (OnePoint.coe_ne_infty 0)
    have hwc0 : (weylEl F * c) ((0 : F) : P1 F) = ((0 : F) : P1 F) := by
      rw [Equiv.Perm.mul_apply, h, weyl_infty]
    have hwcinf : (weylEl F * c) (∞ : P1 F) = ∞ := by
      rw [Equiv.Perm.mul_apply, hcinf', weyl_zero]
    exact pglImage_fixing_zero_infty F (weylEl F * c)
      (Subgroup.mul_mem _ (pslImage_le_pglImage F (weylEl_mem F)) hc) hwc0 hwcinf

end Work.DSTR.M110.SplitAux
