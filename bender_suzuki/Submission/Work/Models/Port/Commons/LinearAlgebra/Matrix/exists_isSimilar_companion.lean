import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Matrix

namespace Commons.LinearAlgebra.Matrix

/-- The value of `Matrix.GeneralLinearGroup.mkOfDetNeZero`. -/
lemma mkOfDetNeZero_coe_eq {F : Type*} [Field F] {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix n n F) (h : M.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero M h : Matrix.GeneralLinearGroup n F) :
      Matrix n n F) = M := rfl

/-- Conjugation criterion: if `A * M = M * C` with `M` invertible, then `A` and `C` are conjugate
by an element of `GL(2,F)`. -/
lemma exists_gl_conj_of_mul_eq {F : Type*} [Field F]
    {A C M : Matrix (Fin 2) (Fin 2) F} (hM : M.det ≠ 0) (hAM : A * M = M * C) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) F,
      (P : Matrix (Fin 2) (Fin 2) F) * A *
        ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = C := by
  refine ⟨(Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)⁻¹, ?_⟩
  simp only [Matrix.GeneralLinearGroup.coe_inv, mkOfDetNeZero_coe_eq]
  rw [Matrix.nonsing_inv_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)]
  calc M⁻¹ * A * M = M⁻¹ * (A * M) := by rw [mul_assoc]
    _ = M⁻¹ * (M * C) := by rw [hAM]
    _ = C := Matrix.nonsing_inv_mul_cancel_left (A := M) C (isUnit_iff_ne_zero.mpr hM)

/-- Explicit similarity to the companion matrix for `2 × 2` matrices of determinant `1` that are
not scalar, expressed in terms of the four entries. -/
lemma exists_isSimilar_companion_aux {F : Type*} [Field F] (a b c d : F)
    (hdet : a * d - b * c = 1) (hnc : ¬(b = 0 ∧ c = 0 ∧ a = d)) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) F,
      (P : Matrix (Fin 2) (Fin 2) F) * !![a, b; c, d] *
        ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = !![0, -1; 1, a + d] := by
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · have had : a ≠ d := fun hd => hnc ⟨hb, hc, hd⟩
      subst hb
      subst hc
      refine exists_gl_conj_of_mul_eq (M := !![1, a; 1, d]) ?_ ?_
      · simp [Matrix.det_fin_two]
        exact sub_ne_zero.mpr had.symm
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          linear_combination -hdet
    · refine exists_gl_conj_of_mul_eq (M := !![1, a; 0, c]) ?_ ?_
      · simp [Matrix.det_fin_two]
        exact hc
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | linear_combination -hdet | ring
  · refine exists_gl_conj_of_mul_eq (M := !![0, b; 1, d]) ?_ ?_
    · simp [Matrix.det_fin_two]
      exact hb
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hdet | ring

theorem exists_isSimilar_companion {F : Type*} [Field F] (A : Matrix (Fin 2) (Fin 2) F) (h : A.det = 1)
    (hnc : ∀ c : F, A ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) F,
      (P : Matrix (Fin 2) (Fin 2) F) * A * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = !![0, -1; 1, A.trace] := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h' := h
    rw [Matrix.eta_fin_two A, Matrix.det_fin_two] at h'
    simpa using h'
  have hnc' : ¬ (A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1) := by
    rintro ⟨h01, h10, h00⟩
    refine hnc (A 0 0) ?_
    rw [Matrix.eta_fin_two A, h01, h10, ← h00]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have htr : A.trace = A 0 0 + A 1 1 := Matrix.trace_fin_two A
  obtain ⟨P, hP⟩ := exists_isSimilar_companion_aux (A 0 0) (A 0 1) (A 1 0) (A 1 1) hdet hnc'
  refine ⟨P, ?_⟩
  rw [htr]
  conv_lhs => rw [Matrix.eta_fin_two A]
  exact hP

end Commons.LinearAlgebra.Matrix
