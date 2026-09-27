import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag

namespace Work.EKLContract.Lemmas

open Work.EKLContract

/-! ## Conjugation of a transvection by a diagonal matrix

`u_ij(s) = 1 + s E_ij` is the transvection of `SL₃(ℝ)`; conjugating it by diagonal matrices
`diag d`, `diag e` with `d k * e k = 1` produces the transvection with parameter `d i * s * e j`.
This is the reason `α^t u_ij(s) α^{-t} = u_ij(e^{t i - t j} s)`. -/

lemma diagonal_single_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (d e : ι → ℝ) {i j : ι}
    (h : i ≠ j) (s : ℝ) (hde : ∀ k, d k * e k = 1) :
    Matrix.diagonal d * (1 + Matrix.single i j s) * Matrix.diagonal e
      = 1 + Matrix.single i j (d i * s * e j) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    by_cases hij : i = a ∧ j = a
    · exfalso
      obtain ⟨h1, h2⟩ := hij
      exact h (by rw [h1, h2])
    · rw [if_neg hij]
      rw [if_neg hij]
      simp only [add_zero, mul_one, hde a]
  · rw [if_neg hab]
    by_cases hija : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hija
      simp
    · rw [if_neg hija]
      rw [if_neg hija]
      ring

/-- The underlying matrix of `u_ij(s)` is `1 + s E_ij`. -/
lemma toMat_uij {i j : Fin 3} (h : i ≠ j) (s : ℝ) :
    toMat (uij h s) = 1 + Matrix.single i j s := by
  rw [uij]
  exact Matrix.SpecialLinearGroup.transvection_coe h s

/-- The scalar factor in the conjugation identity `α^t u_ij(s) α^{-t} = u_ij(e^{t i - t j} s)`. -/
lemma exp_aDiag_scalar (t : Fin 3 → ℝ) (i j : Fin 3) (s : ℝ) :
    Real.exp (t i - (∑ k, t k) / 3) * s * (Real.exp (t j - (∑ k, t k) / 3))⁻¹
      = Real.exp (t i - t j) * s := by
  have h1 : Real.exp (t i - (∑ k, t k) / 3) * (Real.exp (t j - (∑ k, t k) / 3))⁻¹
      = Real.exp (t i - t j) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc, mul_comm s _, ← mul_assoc, h1]

/-- The diagonal factor of `aDiag (-t)` is the pointwise inverse of the diagonal factor of
`aDiag t`. -/
lemma aDiag_neg_diag (t : Fin 3 → ℝ) :
    (fun k : Fin 3 => Real.exp ((-t) k - (∑ j, (-t) j) / 3))
      = (fun k : Fin 3 => (Real.exp (t k - (∑ j, t j) / 3))⁻¹) := by
  funext k
  rw [← Real.exp_neg]
  congr 1
  simp only [Pi.neg_apply, Finset.sum_neg_distrib]
  ring

theorem aDiag_conj_uij (t : Fin 3 → ℝ) {i j : Fin 3} (h : i ≠ j) (s : ℝ) : Work.EKLContract.aDiag t * Work.EKLContract.uij h s * (Work.EKLContract.aDiag t)⁻¹ = Work.EKLContract.uij h (Real.exp (t i - t j) * s) := by
  have hinv : (aDiag t)⁻¹ = aDiag (-t) := inv_eq_of_mul_eq_one_left (aDiag_neg_mul t)
  rw [hinv]
  apply ext_toMat
  simp only [toMat_mul, toMat_aDiag, toMat_uij]
  rw [aDiag_neg_diag]
  rw [diagonal_single_conj (fun k : Fin 3 => Real.exp (t k - (∑ j, t j) / 3))
        (fun k : Fin 3 => (Real.exp (t k - (∑ j, t j) / 3))⁻¹) h s
        (fun k => mul_inv_cancel₀ (Real.exp_ne_zero _))]
  rw [exp_aDiag_scalar]

end Work.EKLContract.Lemmas
