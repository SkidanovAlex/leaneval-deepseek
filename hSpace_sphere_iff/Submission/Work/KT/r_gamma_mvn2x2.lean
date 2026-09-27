import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT

/-- An explicit Murray--von Neumann equivalence between a `2 × 2` matrix `P` over a field with
trace `1` and vanishing determinant `P 0 0 * P 1 1 = P 0 1 * P 1 0`, and the `1 × 1` identity
matrix.

If `P 0 0 ≠ 0` the row `(1, P 0 1 / P 0 0)` and the column `(P 0 0, P 1 0)` give the equivalence;
if `P 0 0 = 0` then `P 1 1 = 1` and one uses the row `(P 1 0, 1)` and the column `(P 0 1, 1)`. -/
theorem r_gamma_mvn2x2 {K : Type} [Field K] (P : Matrix (Fin 2) (Fin 2) K)
    (htr : P 0 0 + P 1 1 = 1) (hdet : P 0 0 * P 1 1 = P 0 1 * P 1 0) :
    Work.KT.Mat.MvN (⟨2, P⟩ : Work.KT.Mat K) (Work.KT.Mat.one K 1) := by
  by_cases h00 : P 0 0 = 0
  · -- Case `P 0 0 = 0`: then `P 1 1 = 1` and the second row/column trivialise `P`.
    have h11 : P 1 1 = 1 := by have h := htr; rw [h00, zero_add] at h; exact h
    have hz : P 0 1 * P 1 0 = 0 := by
      have h := hdet; rw [h00, h11, zero_mul] at h; exact h.symm
    have hz' : P 1 0 * P 0 1 = 0 := by rw [mul_comm]; exact hz
    let a : Matrix (Fin 1) (Fin 2) K := fun _ j => P 1 j
    let b : Matrix (Fin 2) (Fin 1) K := fun i _ => P i 1
    have hba : b * a = P := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_one]
      all_goals simp only [a, b]; simp [h00, h11, hz]
    have hab : a * b = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      simp only [a, b]
      simp [hz', h11]
    exact ⟨a, b, hba, hab⟩
  · -- Case `P 0 0 ≠ 0`: the first row/column trivialise `P`.
    have hx : P 0 0 ≠ 0 := h00
    let a : Matrix (Fin 1) (Fin 2) K := fun _ j => P 0 j / P 0 0
    let b : Matrix (Fin 2) (Fin 1) K := fun i _ => P i 0
    have hba : b * a = P := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_one]
      · simp only [a, b, Fin.mk_zero, Fin.mk_one]; rw [div_self hx, mul_one]
      · simp only [a, b, Fin.mk_zero, Fin.mk_one]
        rw [mul_div_assoc', mul_div_cancel_left₀ (P 0 1) hx]
      · simp only [a, b, Fin.mk_zero, Fin.mk_one]; rw [div_self hx, mul_one]
      · simp only [a, b, Fin.mk_zero, Fin.mk_one]
        rw [mul_div_assoc', mul_comm (P 1 0) (P 0 1), ← hdet,
          mul_div_cancel_left₀ (P 1 1) hx]
    have hab : a * b = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      simp only [a, b, Fin.mk_zero, Fin.mk_one]
      rw [div_self hx, one_mul, div_mul_eq_mul_div, ← hdet,
        mul_div_cancel_left₀ (P 1 1) hx, htr]
      simp
    exact ⟨a, b, hba, hab⟩

end Work.KT
