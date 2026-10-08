import Mathlib
import Submission.Work.AUTL2.Defs

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Aut

/-- An element of `GL(2,F)` that acts trivially on the projective line `ℙ¹(F) = P1 F` is a
scalar matrix.  Reading off the action on `∞`, `0` and `1` determines the matrix. -/
lemma eq_scalar_of_forall_smul_eq_self (F : Type*) [Field F] [DecidableEq F] (g : GL (Fin 2) F)
    (h : ∀ c : OnePoint F, g • c = c) :
    ∃ u : Fˣ, g = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    OnePoint.smul_infty_eq_self_iff.mp (h ∞)
  have h0 := h ((0 : F) : OnePoint F)
  rw [OnePoint.smul_some_eq_ite] at h0
  have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h11
    simp only [h10, mul_zero, zero_add, h11] at h0
    simp at h0
  have h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    simp only [h10, mul_zero, zero_add, h11, ite_false, OnePoint.coe_eq_coe] at h0
    rcases div_eq_zero_iff.mp h0 with h' | h'
    · exact h'
    · exact absurd h' h11
  have h1 := h ((1 : F) : OnePoint F)
  rw [OnePoint.smul_some_eq_ite] at h1
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    simp only [h10, h01, mul_one, zero_add, add_zero, h11, ite_false,
      OnePoint.coe_eq_coe, div_eq_one_iff_eq h11] at h1
    exact h1
  have hmat : (g : Matrix (Fin 2) (Fin 2) F) =
      Matrix.scalar (Fin 2) ((g : Matrix (Fin 2) (Fin 2) F) 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, h10, h01, h00]
  have hmem : g ∈ Subgroup.center (GL (Fin 2) F) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨_, hmat.symm⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem
  obtain ⟨u, hu⟩ := hmem
  exact ⟨u, hu.symm⟩

theorem pglHomInjective (F : Type*) [Field F] [DecidableEq F] :
    Function.Injective (Work.AUTL2.pglHom F) := by
  intro a b hab
  obtain ⟨g1, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective a
  obtain ⟨g2, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective b
  have hfun : ∀ c : P1 F, g1 • c = g2 • c := by
    intro c
    exact congrArg (fun e : Equiv.Perm (P1 F) => (e : P1 F → P1 F) c) hab
  have hfix : ∀ c : P1 F, (g2⁻¹ * g1) • c = c := by
    intro c
    rw [mul_smul, hfun c, inv_smul_smul]
  obtain ⟨u, hu⟩ := eq_scalar_of_forall_smul_eq_self F (g2⁻¹ * g1) hfix
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨u⁻¹, ?_⟩
  have hg1 : g1 = g2 * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    rw [← hu, mul_inv_cancel_left]
  rw [hg1, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

end Work.AUTL2.Aut
