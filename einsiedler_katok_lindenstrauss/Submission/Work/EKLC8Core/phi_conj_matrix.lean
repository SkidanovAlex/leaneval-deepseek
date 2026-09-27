import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-!
# `phi_conj_matrix`: the conjugation action of the diagonal flow `φ_τ`

`φ_τ = aDiag (τ • flowExp)` is the diagonal element `diag(e^{-τ}, e^{τ}, 1) = aDiag(τ • flowExp)`.
Conjugating `g : SL₃(ℝ)` by `φ_τ` therefore rescales the `(i,j)` entry of `g` by the factor
`e^{τ(flowExp i - flowExp j)}`: this is the elementary computation behind the "rate of expansion
of the root groups" used throughout component C8.

The proof unfolds `phi` to the diagonal matrix it is, uses `adjugate_diagonal` for the inverse
(whose diagonal entries are `e^{τ·flowExp i}` and `e^{-τ·flowExp j}` since `∑ flowExp = 0`), and
then reads off the `(i,j)` entry of the product of diagonal matrices.
-/

/-- `∑ flowExp = -1 + 1 + 0 = 0`, so `phi τ = diag(e^{-τ}, e^{τ}, 1)` with no normalisation term. -/
lemma flowExp_sum_zero : (∑ j : Fin 3, flowExp j) = 0 := by
  simp [flowExp, Fin.sum_univ_three]

/-- The sum of `flowExp` over all indices except `i` is `-flowExp i` (used for `adjugate`). -/
lemma sum_erase_flowExp (i : Fin 3) : (∑ j ∈ Finset.univ.erase i, flowExp j) = - flowExp i := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin 3)) flowExp (Finset.mem_univ i)
  have h0 : (∑ j : Fin 3, flowExp j) = 0 := flowExp_sum_zero
  linarith

/-- The underlying matrix of `φ_τ` is `diagonal (fun i => exp (τ * flowExp i))`. -/
lemma phi_mat_coe (τ : ℝ) : ((phi τ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
    = Matrix.diagonal (fun i => Real.exp (τ * flowExp i)) := by
  simp only [phi, aDiag, Matrix.SpecialLinearGroup.coe_mk, Pi.smul_apply, smul_eq_mul,
    flowExp, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [show τ * -1 + τ * 1 + τ * 0 = 0 by ring, zero_div]
  simp only [sub_zero]

/-- The underlying matrix of `φ_τ⁻¹` is `diagonal (fun i => exp (-(τ * flowExp i)))`. -/
lemma phi_inv_coe (τ : ℝ) :
    (((phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.diagonal (fun i => Real.exp (-(τ * flowExp i))) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, phi_mat_coe, Matrix.adjugate_diagonal]
  congr 1
  ext i
  rw [← Real.exp_sum]
  congr 1
  have hmul : (∑ x ∈ Finset.univ.erase i, τ * flowExp x)
      = τ * ∑ x ∈ Finset.univ.erase i, flowExp x := by
    rw [Finset.mul_sum]
  rw [hmul, sum_erase_flowExp, show τ * -flowExp i = -(τ * flowExp i) by ring]

theorem phi_conj_matrix (τ : ℝ) (g : SL3) (i j : Fin 3) :
    ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
      = Real.exp ((flowExp i - flowExp j) * τ) * (g : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      phi_mat_coe, phi_inv_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h : Real.exp (τ * flowExp i) * Real.exp (-(τ * flowExp j))
      = Real.exp ((flowExp i - flowExp j) * τ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_right_comm, h]

end Work.EKLC8Core
