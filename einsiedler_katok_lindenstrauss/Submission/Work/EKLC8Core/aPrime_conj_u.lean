import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.aDiag_add

namespace Work.EKLC8Core

open scoped Matrix

/-!
# `aPrime_conj_u`: conjugation of the unipotent `u(r)` by `a'_{ab}(s)`

`aPrime 2 s = aDiag (fun i => if i = 2 then -2s else s) = diag(e^s, e^s, e^{-2s})` is a
diagonal element of `SL₃(ℝ)`; conjugating a transvection `u_ij(r) = 1 + r E_ij` by a diagonal
element `α^t` rescales the parameter by `e^{t_i - t_j}`.  Here `(i,j) = (0,1)` and the two
exponents are both `s`, so the factor is `e^{s-s} = 1` and `u(r)` is fixed.

The work is the general diagonal-conjugation identity `aDiag_conj_uij`, proved by reading off
the `(i,j)` entry of the product of diagonal matrices.
-/

/-- `diag(d) * (c · E_{ij}) = (d i * c) · E_{ij}`. -/
private lemma diagonal_mul_single (d : Fin 3 → ℝ) (i j : Fin 3) (c : ℝ) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext k l
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply, mul_ite, mul_zero]
  by_cases hkl : i = k ∧ j = l
  · obtain ⟨hk, hl⟩ := hkl; subst hk; subst hl; simp
  · rw [if_neg hkl, if_neg hkl]

/-- `(c · E_{ij}) * diag(d) = (c * d j) · E_{ij}`. -/
private lemma single_mul_diagonal (d : Fin 3 → ℝ) (i j : Fin 3) (c : ℝ) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply, ite_mul, zero_mul]
  by_cases hkl : i = k ∧ j = l
  · obtain ⟨hk, hl⟩ := hkl; subst hk; subst hl; simp
  · rw [if_neg hkl, if_neg hkl]

/-- The underlying matrix of `α^t` is `diag(e^{t_i - (∑t)/3})`. -/
theorem aDiag_coe (t : Fin 3 → ℝ) : ((aDiag t : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
    = Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3)) := rfl

/-- The matrix identity `α^t · u_ij(s) = u_ij(e^{t_i-t_j} s) · α^t`. -/
private lemma aDiag_mul_uij_coe (t : Fin 3 → ℝ) {i j : Fin 3} (h : i ≠ j) (s : ℝ) :
    ((aDiag t : SL3) : Matrix (Fin 3) (Fin 3) ℝ) * ((uij h s : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = ((uij h (Real.exp (t i - t j) * s) : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        * ((aDiag t : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
  have key : Real.exp (t i - t j) * Real.exp (t j - (∑ k, t k) / 3)
      = Real.exp (t i - (∑ k, t k) / 3) := by
    rw [← Real.exp_add]; congr 1; ring
  have hd : Real.exp (t i - (∑ k, t k) / 3) * s
      = Real.exp (t i - t j) * s * Real.exp (t j - (∑ k, t k) / 3) := by
    rw [← key]; ring
  rw [aDiag_coe t]
  simp only [uij, Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      diagonal_mul_single, single_mul_diagonal, hd]

/-- The diagonal element is the identity at the zero exponent. -/
theorem aDiag_zero' : aDiag (0 : Fin 3 → ℝ) = 1 := by
  apply Subtype.ext
  simp [aDiag]

/-- `(α^t)⁻¹ = α^{-t}`. -/
theorem aDiag_inv (t : Fin 3 → ℝ) : (aDiag t)⁻¹ = aDiag (-t) := by
  have h : aDiag t * aDiag (-t) = 1 := by
    rw [← aDiag_add, add_neg_cancel, aDiag_zero']
  exact inv_eq_of_mul_eq_one_right h

/-- Conjugation of a transvection by a diagonal element `α^t` of `SL₃(ℝ)`:
`α^t · u_ij(s) · α^{-t} = u_ij(e^{t_i-t_j} s)`. -/
theorem aDiag_conj_uij (t : Fin 3 → ℝ) {i j : Fin 3} (h : i ≠ j) (s : ℝ) :
    aDiag t * uij h s * (aDiag t)⁻¹ = uij h (Real.exp (t i - t j) * s) := by
  have key : aDiag t * uij h s
      = uij h (Real.exp (t i - t j) * s) * aDiag t := by
    apply Matrix.SpecialLinearGroup.ext
    intro k l
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact congrFun (congrFun (aDiag_mul_uij_coe t h s) k) l
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

/-- The third-index slot of `a'_{ab}(s) = aPrime 2 s`. -/
private def aPrimeExp (s : ℝ) : Fin 3 → ℝ := fun i => if i = 2 then -2 * s else s

/-- The two exponents on the pair `(0,1)` agree, so `a'_{ab}(s)` fixes `u(r)`. -/
theorem aPrime_conj_u (s r : ℝ) : aPrime 2 s * u r * (aPrime 2 s)⁻¹ = u r := by
  have ht : aPrimeExp s 0 - aPrimeExp s 1 = 0 := by
    have h0 : ((0 : Fin 3) = 2) = False := by decide
    have h1 : ((1 : Fin 3) = 2) = False := by decide
    simp only [aPrimeExp, h0, h1]
    norm_num
  have h := aDiag_conj_uij (aPrimeExp s) (h := h01) r
  rw [ht, Real.exp_zero, one_mul] at h
  have hap : aPrime 2 s = aDiag (aPrimeExp s) := rfl
  rw [hap]
  exact h

end Work.EKLC8Core
