/-
# Symmetric tridiagonal matrices with constant off-diagonal `1`

A small library used by `Work.TMC16Core.Basic.dirMat_det` (the Dirichlet determinant of
`H - E` on `n` consecutive sites).  `triDiag d n` is the `n × n` matrix with diagonal
`d 0, …, d (n-1)` and off-diagonal entries `1`; `dirMat α lam θ E n` is the special case
`d k = amoPot α lam θ k - E` (`dirMat_eq_triDiag`, definitionally).
-/
import Mathlib
import Submission.Work.TMC16Core.Defs

noncomputable section

namespace Work.TMC16Core

/-- The `n × n` symmetric tridiagonal matrix with diagonal `d` and off-diagonal `1`:
entry `(i,j)` is `d i` if `i = j`, `1` if `i + 1 = j` or `j + 1 = i`, and `0` otherwise. -/
def triDiag (d : ℕ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (if i = j then d ((i : ℕ)) else 0) +
    (if ((i : ℕ) : ℤ) + 1 = ((j : ℕ) : ℤ) then 1 else 0) +
    (if ((j : ℕ) : ℤ) + 1 = ((i : ℕ) : ℤ) then 1 else 0)

/-- The Dirichlet matrix is the tridiagonal matrix with diagonal `amoPot - E`. -/
theorem dirMat_eq_triDiag (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) :
    dirMat α lam θ E n =
      triDiag (fun k => ((amoPot α lam θ (k : ℤ) : ℝ) : ℂ) - E) n := rfl

/-- The leading principal `n × n` minor of `triDiag d (n+1)`. -/
theorem triDiag_submatrix_castSucc (d : ℕ → ℂ) (n : ℕ) :
    (triDiag d (n + 1)).submatrix Fin.castSucc Fin.castSucc = triDiag d n := by
  ext i j; simp [triDiag, Matrix.submatrix_apply]

/-- The last row of `triDiag d (n+2)`: it is `1` in column `n` and `d (n+1)` in the last
column, and vanishes elsewhere. -/
theorem triDiag_last_row (d : ℕ → ℂ) (n : ℕ) (j : Fin (n + 2)) :
    triDiag d (n + 2) (Fin.last (n + 1)) j =
      (if (j : ℕ) + 1 = n + 1 then 1 else 0) + (if (j : ℕ) = n + 1 then d (n + 1) else 0) := by
  simp only [triDiag, Fin.val_last]
  have h2 : ¬ ((↑(n + 1) : ℤ) + 1 = ((j : ℕ) : ℤ)) := by omega
  rw [if_neg h2, add_zero]
  by_cases hE : (j : ℕ) + 1 = n + 1
  · have hB : ((j : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    have hA : ¬ (Fin.last (n + 1) = j) := by
      intro hh; have := congrArg Fin.val hh; simp at this; omega
    have hC : ¬ ((j : ℕ) = n + 1) := by omega
    rw [if_neg hA, if_pos hB, if_pos hE, if_neg hC]; simp
  · have hB : ¬ (((j : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ)) := by omega
    by_cases hj : (j : ℕ) = n + 1
    · have hA : Fin.last (n + 1) = j := Fin.ext (by simpa using hj.symm)
      rw [if_pos hA, if_neg hB, if_neg hE, if_pos hj]; simp
    · have hA : ¬ (Fin.last (n + 1) = j) := by
        intro hh; have := congrArg Fin.val hh; simp at this; omega
      rw [if_neg hA, if_neg hB, if_neg hE, if_neg hj]

theorem negOnePow_two_mul (n : ℕ) : (-1 : ℂ) ^ (2 * n) = 1 := by
  rw [pow_mul]; norm_num

theorem negOnePow_two_mul_add_one (n : ℕ) : (-1 : ℂ) ^ (2 * n + 1) = -1 := by
  rw [pow_succ, negOnePow_two_mul]; norm_num

theorem det_updateCol_last_single (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (A.updateCol (Fin.last n) (Pi.single (Fin.last n) (1 : ℂ))).det =
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_column _ (Fin.last n)]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [Fin.succAbove_last]
    have hsub : (A.updateCol (Fin.last n) (Pi.single (Fin.last n) (1 : ℂ))).submatrix
          Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc := by
      ext i k
      rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.updateCol_apply,
        if_neg (Fin.castSucc_ne_last k)]
    rw [hsub, Matrix.updateCol_self, Pi.single_eq_same,
      show (↑(Fin.last n) + ↑(Fin.last n) : ℕ) = 2 * n by simp [Fin.val_last]; ring,
      negOnePow_two_mul]
    ring
  · intro b _ hb
    rw [Matrix.updateCol_self, Pi.single_eq_of_ne hb]
    ring
  · intro h; exact absurd (Finset.mem_univ _) h

theorem triDiag_symm (d : ℕ → ℂ) (n : ℕ) (i j : Fin n) : triDiag d n i j = triDiag d n j i := by
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : ¬ (j = i) := fun h => hij h.symm
    rw [triDiag, triDiag, if_neg hij, if_neg hji]
    simp only [zero_add]
    exact add_comm _ _

theorem triDiag_submatrix_updateCol (d : ℕ → ℂ) (n : ℕ) :
    (triDiag d (n + 2)).submatrix Fin.castSucc
        (Fin.succAbove ((Fin.last n).castSucc : Fin (n + 2))) =
      (triDiag d (n + 1)).updateCol (Fin.last n) (Pi.single (Fin.last n) (1 : ℂ)) := by
  ext i k
  rw [Matrix.submatrix_apply, Matrix.updateCol_apply]
  rcases lt_or_ge k (Fin.last n) with hk | hk
  · rw [Fin.succAbove_castSucc_of_lt _ _ hk, if_neg (Fin.ne_of_lt hk)]
    have h := congrFun (congrFun (triDiag_submatrix_castSucc d (n + 1)) i) k
    simpa [Matrix.submatrix_apply] using h
  · have hk' : k = Fin.last n := le_antisymm (Fin.le_last k) hk
    subst hk'
    rw [Fin.succAbove_castSucc_self, if_pos rfl]
    rw [show ((Fin.last n).succ : Fin (n + 2)) = Fin.last (n + 1) from by ext; simp]
    rw [triDiag_symm]
    by_cases hi : i = Fin.last n
    · subst hi
      rw [Pi.single_eq_same, triDiag_last_row]
      have hv : (((Fin.last n).castSucc : Fin (n + 2)) : ℕ) = n := by simp
      rw [hv, if_pos rfl, if_neg (by omega)]
      simp
    · rw [Pi.single_eq_of_ne hi, triDiag_last_row]
      have hv : ((Fin.castSucc i : Fin (n + 2)) : ℕ) = (i : ℕ) := by simp
      have hilt : (i : ℕ) < n := by
        have h1 : (i : ℕ) < n + 1 := i.isLt
        have h2 : (i : ℕ) ≠ n := by
          intro h; exact hi (Fin.ext (by simpa [Fin.val_last] using h))
        omega
      rw [hv, if_neg (by omega), if_neg (by omega)]
      simp

theorem triDiag_det_recur (d : ℕ → ℂ) (n : ℕ) :
    (triDiag d (n + 2)).det = d (n + 1) * (triDiag d (n + 1)).det - (triDiag d n).det := by
  have hzero : (∑ i : Fin n,
        (-1 : ℂ) ^ ((Fin.last (n + 1) : ℕ) + (i.castSucc.castSucc : ℕ)) *
            triDiag d (n + 2) (Fin.last (n + 1)) i.castSucc.castSucc *
          ((triDiag d (n + 2)).submatrix (Fin.last (n + 1)).succAbove
            i.castSucc.castSucc.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [triDiag_last_row]
    have h1 : ¬ (((i.castSucc.castSucc : Fin (n + 2)) : ℕ) + 1 = n + 1) := by simp; omega
    have h2 : ¬ (((i.castSucc.castSucc : Fin (n + 2)) : ℕ) = n + 1) := by simp; omega
    rw [if_neg h1, if_neg h2]
    simp
  have hJrow : triDiag d (n + 2) (Fin.last (n + 1)) ((Fin.last n).castSucc) = 1 := by
    rw [triDiag_last_row]
    have hv : (((Fin.last n).castSucc : Fin (n + 2)) : ℕ) = n := by simp
    rw [hv, if_pos rfl, if_neg (by omega)]
    simp
  have hLrow : triDiag d (n + 2) (Fin.last (n + 1)) (Fin.last (n + 1)) = d (n + 1) := by
    rw [triDiag_last_row]
    have hv : ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) = n + 1 := by simp
    rw [hv, if_neg (by omega), if_pos rfl]
    simp
  have hJminor : ((triDiag d (n + 2)).submatrix (Fin.last (n + 1)).succAbove
        ((Fin.last n).castSucc).succAbove).det = (triDiag d n).det := by
    rw [Fin.succAbove_last, triDiag_submatrix_updateCol, det_updateCol_last_single,
      triDiag_submatrix_castSucc]
  have hLminor : ((triDiag d (n + 2)).submatrix (Fin.last (n + 1)).succAbove
        (Fin.last (n + 1)).succAbove).det = (triDiag d (n + 1)).det := by
    rw [Fin.succAbove_last, triDiag_submatrix_castSucc]
  have hJsign : (-1 : ℂ) ^ ((Fin.last (n + 1) : ℕ) + ((Fin.last n).castSucc : ℕ)) = -1 := by
    rw [show ((Fin.last (n + 1) : ℕ) + ((Fin.last n).castSucc : ℕ)) = 2 * n + 1 by
      simp; ring, negOnePow_two_mul_add_one]
  have hLsign : (-1 : ℂ) ^ ((Fin.last (n + 1) : ℕ) + (Fin.last (n + 1) : ℕ)) = 1 := by
    rw [show ((Fin.last (n + 1) : ℕ) + (Fin.last (n + 1) : ℕ)) = 2 * (n + 1) by
      simp; ring, negOnePow_two_mul]
  rw [Matrix.det_succ_row _ (Fin.last (n + 1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
    hzero, zero_add, hJsign, hLsign, hJrow, hLrow, hJminor, hLminor]
  ring

end Work.TMC16Core

end
