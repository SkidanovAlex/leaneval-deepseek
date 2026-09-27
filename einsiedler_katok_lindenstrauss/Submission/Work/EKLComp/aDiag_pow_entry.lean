import Mathlib
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLProd.aDiag_nsmul

/-!
# Entries of a power of `aDiag t`, conjugated

The element `α^t = aDiag t` of `SL₃(ℝ)` is diagonal, and every conjugate of an element by `α^t`
is obtained by scaling the `(i,j)`-entry by `e^{t_i - t_j}`.  This module records the corresponding
computation for powers `(aDiag t)^n`, namely that conjugation by `(aDiag t)^n` scales the
`(i,j)`-entry by `e^{n(t_i - t_j)}`.

The proof is a two-line matrix computation: `(aDiag t)^n = aDiag (n • t)` (a diagonal matrix),
and for diagonal `D`, `E` one has `(D * M * E) i j = D i i * M i j * E j j`; the two diagonal
factors `e^{n t_i - (∑ n t)/3}` and `e^{-n t_j + (∑ n t)/3}` multiply to `e^{n(t_i - t_j)}`.
-/

namespace Work.EKLComp

open Work.EKLContract

/-- Entries of a product of a matrix with diagonal matrices on either side. -/
private lemma diagonal_conj_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d e : ι → ℝ) (M : Matrix ι ι ℝ) (i j : ι) :
    (Matrix.diagonal d * M * Matrix.diagonal e) i j = d i * M i j * e j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Conjugation by the diagonal element `aDiag s` scales the `(i,j)`-entry by `e^{s i - s j}`. -/
private lemma aDiag_conj_entry (s : Fin 3 → ℝ) (u : SL3) (i j : Fin 3) :
    toMat (aDiag s * u * (aDiag s)⁻¹) i j = Real.exp (s i - s j) * toMat u i j := by
  have hinv : (aDiag s)⁻¹ = aDiag (-s) := inv_eq_of_mul_eq_one_left (aDiag_neg_mul s)
  rw [hinv, toMat_mul, toMat_mul, toMat_aDiag, toMat_aDiag]
  rw [diagonal_conj_apply]
  have h1 : Real.exp (s i - (∑ k, s k) / 3) * Real.exp ((-s) j - (∑ k, (-s) k) / 3)
      = Real.exp (s i - s j) := by
    rw [← Real.exp_add]
    congr 1
    simp only [Pi.neg_apply, Finset.sum_neg_distrib]
    ring
  rw [← h1]
  ring

/-- Conjugation by a power `(aDiag t)^n` scales the `(i,j)`-entry by `e^{n(t i - t j)}`. -/
theorem aDiag_pow_entry (t : Fin 3 → ℝ) (n : ℕ) (u : Work.EKLContract.SL3)
    (i j : Fin 3) :
    Work.EKLContract.toMat (Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹) i j
      = Real.exp ((n : ℝ) * (t i - t j)) * Work.EKLContract.toMat u i j := by
  rw [← Work.EKLProd.aDiag_nsmul t n]
  rw [aDiag_conj_entry]
  have h : Real.exp ((n • t) i - (n • t) j) = Real.exp ((n : ℝ) * (t i - t j)) := by
    congr 1
    simp [Pi.smul_apply, nsmul_eq_mul]
    ring
  rw [h]

end Work.EKLComp
