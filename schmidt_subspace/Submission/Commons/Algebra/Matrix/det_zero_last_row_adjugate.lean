import Mathlib

open Matrix

namespace Commons.Algebra.Matrix

variable {R : Type*} [CommRing R]

/-- Auxiliary index identity: the successor-above embedding followed by the map removing `l`
agrees with `castSucc` after removing `l` on the smaller index. -/
lemma fin_succAbove_castSucc_comp {m : ℕ} (l : Fin (m+1)) (k : Fin m) :
    (Fin.castSucc l).succAbove (Fin.castSucc k) = Fin.castSucc (l.succAbove k) := by
  rcases lt_or_ge (k : ℕ) (l : ℕ) with h | h
  · rw [Fin.succAbove_of_castSucc_lt (Fin.castSucc l) (Fin.castSucc k)
        (by simp only [Fin.lt_def, Fin.val_castSucc]; exact h),
      Fin.succAbove_of_castSucc_lt l k (by simp only [Fin.lt_def, Fin.val_castSucc]; exact h)]
  · rw [Fin.succAbove_of_le_castSucc (Fin.castSucc l) (Fin.castSucc k)
        (by simp only [Fin.le_def, Fin.val_castSucc]; exact h),
      Fin.succAbove_of_le_castSucc l k (by simp only [Fin.le_def, Fin.val_castSucc]; exact h)]
    rfl

lemma fin_succAbove_castSucc_last {m : ℕ} (l : Fin (m+1)) :
    (Fin.castSucc l).succAbove (Fin.last m) = Fin.last (m+1) := by
  rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]
    exact Nat.le_of_lt_succ l.isLt

/-- The `(l,last)`-cofactor of an `(m+2)×(m+2)` matrix is minus the `l`-th Cramer
combination of the top-left `(m+1)×(m+1)` minor. -/
lemma adjugate_castSucc_last {m : ℕ} (M : Matrix (Fin (m + 2)) (Fin (m + 2)) R)
    (l : Fin (m + 1)) :
    M.adjugate (Fin.castSucc l) (Fin.last (m + 1)) =
      - ((M.submatrix Fin.castSucc Fin.castSucc).adjugate *ᵥ
          (fun i => M (Fin.castSucc i) (Fin.last (m + 1)))) l := by
  set A : Matrix (Fin (m+1)) (Fin (m+1)) R := M.submatrix Fin.castSucc Fin.castSucc with hA
  set b : Fin (m+1) → R := fun i => M (Fin.castSucc i) (Fin.last (m+1)) with hb
  set N : Matrix (Fin (m+1)) (Fin (m+1)) R := M.submatrix Fin.castSucc ((Fin.castSucc l).succAbove)
    with hN
  have hsub : ∀ i : Fin (m+1),
      N.submatrix i.succAbove (Fin.last m).succAbove = A.submatrix i.succAbove l.succAbove := by
    intro i
    ext a c
    simp only [hN, hA, Matrix.submatrix_apply]
    rw [Fin.succAbove_last_apply, fin_succAbove_castSucc_comp l c]
  have hdetN : N.det = ∑ i : Fin (m+1),
      b i * ((-1 : R) ^ ((i:ℕ) + m) * (A.submatrix i.succAbove l.succAbove).det) := by
    rw [Matrix.det_eq_sum_mul_adjugate_col N (Fin.last m)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix N (Fin.last m) i, hsub i]
    rw [show N i (Fin.last m) = b i from by
      simp only [hN, hb, Matrix.submatrix_apply]
      rw [fin_succAbove_castSucc_last l]]
    simp only [Fin.val_last]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix M (Fin.castSucc l) (Fin.last (m + 1))]
  rw [Fin.succAbove_last]
  rw [hdetN]
  rw [Matrix.mulVec_apply_eq_sum]
  rw [Finset.mul_sum]
  have hterm : ∀ i : Fin (m+1),
      (-1 : R) ^ ((Fin.last (m+1) : ℕ) + (Fin.castSucc l : ℕ)) *
        (b i * ((-1 : R) ^ ((i:ℕ) + m) * (A.submatrix i.succAbove l.succAbove).det))
      = -((A.adjugate l i) * b i) := by
    intro i
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix A l i]
    have hsign : (-1 : R) ^ ((Fin.last (m+1) : ℕ) + (Fin.castSucc l : ℕ)) *
          (-1 : R) ^ ((i:ℕ) + m)
        = -((-1 : R) ^ ((i:ℕ) + l)) := by
      rw [← pow_add]
      have hexp : (Fin.last (m+1) : ℕ) + (Fin.castSucc l : ℕ) + ((i:ℕ) + m)
          = ((i:ℕ) + l) + 1 + 2*m := by
        simp only [Fin.val_last, Fin.val_castSucc]; omega
      rw [hexp, pow_add, Even.neg_one_pow (even_two_mul m), mul_one, pow_add, pow_one]
      ring
    linear_combination (b i * (A.submatrix i.succAbove l.succAbove).det) * hsign
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_neg_distrib]

/-- The `(last,last)`-cofactor of an `(m+2)×(m+2)` matrix is the top-left minor. -/
lemma adjugate_last_last {m : ℕ} (M : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    M.adjugate (Fin.last (m + 1)) (Fin.last (m + 1)) =
      (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix M (Fin.last (m+1)) (Fin.last (m+1)),
    Fin.succAbove_last]
  have hexp : (Fin.last (m+1) : ℕ) + (Fin.last (m+1) : ℕ) = 2 * (m+1) := by
    simp only [Fin.val_last]; omega
  rw [hexp, Even.neg_one_pow (even_two_mul (m+1)), one_mul]

/-- The last row is a Cramer combination of the first rows, up to the determinant. -/
lemma sum_mul_adjugate_eq_det_sub {m : ℕ} (M : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    (∑ l : Fin (m+1), M (Fin.last (m+1)) (Fin.castSucc l) *
        (Matrix.mulVec (M.submatrix Fin.castSucc Fin.castSucc).adjugate
          (fun i : Fin (m+1) => M (Fin.castSucc i) (Fin.last (m+1)))) l)
      = (M.submatrix Fin.castSucc Fin.castSucc).det * M (Fin.last (m+1)) (Fin.last (m+1))
        - M.det := by
  set A : Matrix (Fin (m+1)) (Fin (m+1)) R := M.submatrix Fin.castSucc Fin.castSucc with hA
  set b : Fin (m+1) → R := fun i => M (Fin.castSucc i) (Fin.last (m+1)) with hb
  have key := Matrix.det_eq_sum_mul_adjugate_row M (Fin.last (m+1))
  rw [Fin.sum_univ_castSucc] at key
  rw [adjugate_last_last M] at key
  rw [show (∑ i : Fin (m+1), M (Fin.last (m+1)) (Fin.castSucc i) *
        M.adjugate (Fin.castSucc i) (Fin.last (m+1)))
      = ∑ i : Fin (m+1), M (Fin.last (m+1)) (Fin.castSucc i) * (-(A.adjugate *ᵥ b) i) from
        Finset.sum_congr rfl (fun i _ => by rw [adjugate_castSucc_last M i])] at key
  have hneg : (∑ i : Fin (m+1), M (Fin.last (m+1)) (Fin.castSucc i) * (-(A.adjugate *ᵥ b) i))
      = - ∑ i : Fin (m+1), M (Fin.last (m+1)) (Fin.castSucc i) * (A.adjugate *ᵥ b) i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hneg] at key
  rw [key]
  ring

/-- **Last row as a Cramer combination of the previous rows.**

Let `M` be an `(n+1) × (n+1)` matrix over a commutative ring with `M.det = 0`, and suppose the
top-left `n × n` minor `A := M.submatrix Fin.castSucc Fin.castSucc` has `A.det ≠ 0`.  Put
`C := A.adjugate *ᵥ (fun i => M (Fin.castSucc i) (Fin.last n))`.  Then the last row of `M` is the
corresponding combination of the first `n` rows multiplied by `A.det`:
`∑_l M (last) (castSucc l) * C_l = A.det * M (last) (last)`. -/
theorem det_zero_last_row_adjugate {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : M.det = 0)
    (hD : (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0) :
    (∑ l : Fin n, M (Fin.last n) (Fin.castSucc l) *
        (Matrix.mulVec (M.submatrix Fin.castSucc Fin.castSucc).adjugate
          (fun i : Fin n => M (Fin.castSucc i) (Fin.last n))) l)
      = (M.submatrix Fin.castSucc Fin.castSucc).det * M (Fin.last n) (Fin.last n) := by
  rcases n with _ | m
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Matrix.det_fin_zero, one_mul]
    simpa [Matrix.det_fin_one] using hM.symm
  · have hgen := sum_mul_adjugate_eq_det_sub M
    rw [hM, sub_zero] at hgen
    exact hgen

end Commons.Algebra.Matrix
