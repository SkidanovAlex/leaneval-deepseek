/-
  WilE4 / CAD — the entry formula for the principal subresultant matrix.

  `Work.WilE4.CAD.pscMat f g m n i` is the submatrix of the Sylvester matrix `sylvester f g m n`
  on the rows `pscRow m n i` (the powers `X ^ (2 * i), …, X ^ (m + n - 1)`) and the columns
  `pscCol m n i` (the multiples `X ^ k * f` for `i ≤ k ≤ n - 1`, then `X ^ k * g` for
  `i ≤ k ≤ m - 1`).

  This file computes its entries.  If the column index `k` lies in the first block
  (`k < n - i`, so that the column is the multiple `X ^ (i + k) * f`) then, up to the fact that
  the row index `2 * i + r` of the Sylvester matrix records the coefficient of `X ^ (2 * i + r)`,

    `pscMat f g m n i r k = (f * X ^ k).coeff (i + r)`,

  while if `k ≥ n - i` (the column is `X ^ (i + (k - (n - i))) * g`)

    `pscMat f g m n i r k = (g * X ^ (k - (n - i))).coeff (i + r)`.

  (The `i` of the row shift is absorbed: the coefficient of `X ^ (2 * i + r)` in `X ^ (i + k) * f`
  equals the coefficient of `X ^ (i + r)` in `X ^ k * f`.)  These are exactly the entries of the
  matrix, in the standard monomial bases, of the linear map
  `(A, B) ↦ (r ↦ (A * f + B * g).coeff (i + r))` on `ℝ[X]_{< n - i} × ℝ[X]_{< m - i}`.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Proj

set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open Polynomial Matrix

/-- The `f`-half of the Sylvester matrix: the entry of the column `X ^ j * f` of
`Polynomial.sylvester f g m n`, for `j : Fin n`. -/
lemma sylvester_natAdd_apply (f g : ℝ[X]) (m n : ℕ) (ir : Fin (m + n)) (j : Fin n) :
    (Polynomial.sylvester f g m n) ir (Fin.natAdd m j)
      = if ((ir : ℕ) ∈ Set.Icc (j : ℕ) (j + m)) then f.coeff ((ir : ℕ) - (j : ℕ)) else 0 := by
  rw [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]

/-- The `g`-half of the Sylvester matrix: the entry of the column `X ^ j * g` of
`Polynomial.sylvester f g m n`, for `j : Fin m`. -/
lemma sylvester_castAdd_apply (f g : ℝ[X]) (m n : ℕ) (ir : Fin (m + n)) (j : Fin m) :
    (Polynomial.sylvester f g m n) ir (Fin.castAdd n j)
      = if ((ir : ℕ) ∈ Set.Icc (j : ℕ) (j + n)) then g.coeff ((ir : ℕ) - (j : ℕ)) else 0 := by
  rw [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]

/-- **The entries of the principal subresultant matrix.**  Row `r` of `pscMat f g m n i` records
the coefficients of `X ^ (i + r)`; the `f`-block of the columns is indexed by the shift `k`
(`0 ≤ k < n - i`) and the `g`-block by `k - (n - i)`. -/
lemma pscMat_apply (f g : ℝ[X]) {m n i : ℕ} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (r k : Fin (m + n - 2 * i)) :
    pscMat f g m n i r k =
      if (k : ℕ) < n - i then (f * X ^ (k : ℕ)).coeff (i + (r : ℕ))
      else (g * X ^ ((k : ℕ) - (n - i))).coeff (i + (r : ℕ)) := by
  by_cases hk : (k : ℕ) < n - i
  · rw [ite_eq_left hk]
    have hcol : pscCol m n i k = Fin.natAdd m ⟨i + (k : ℕ), by omega⟩ := by
      rw [pscCol, dite_eq_left hk]
      ext
      simp only [Fin.val_natAdd]
      omega
    rw [pscMat, Matrix.submatrix_apply, hcol, sylvester_natAdd_apply]
    simp only [pscRow, Set.mem_Icc]
    rw [coeff_mul_X_pow']
    by_cases h1 : i + (k : ℕ) ≤ 2 * i + (r : ℕ) ∧ 2 * i + (r : ℕ) ≤ i + (k : ℕ) + m
    · rw [ite_eq_left h1, ite_eq_left (by omega : (k : ℕ) ≤ i + (r : ℕ))]
      congr 1
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : (k : ℕ) ≤ i + (r : ℕ)
      · rw [ite_eq_left h2]
        have hm : m < i + (r : ℕ) - (k : ℕ) := by
          by_contra hcon
          exact h1 ⟨by omega, by omega⟩
        exact (coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf hm)).symm
      · rw [ite_eq_right h2]
  · rw [ite_eq_right hk]
    have hcol : pscCol m n i k = Fin.castAdd n ⟨i + ((k : ℕ) - (n - i)), by omega⟩ := by
      rw [pscCol, dite_eq_right hk]
      ext
      simp only [Fin.val_castAdd]
    rw [pscMat, Matrix.submatrix_apply, hcol, sylvester_castAdd_apply]
    simp only [pscRow, Set.mem_Icc]
    rw [coeff_mul_X_pow']
    by_cases h1 : i + ((k : ℕ) - (n - i)) ≤ 2 * i + (r : ℕ) ∧
        2 * i + (r : ℕ) ≤ i + ((k : ℕ) - (n - i)) + n
    · rw [ite_eq_left h1, ite_eq_left (by omega : ((k : ℕ) - (n - i)) ≤ i + (r : ℕ))]
      congr 1
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : ((k : ℕ) - (n - i)) ≤ i + (r : ℕ)
      · rw [ite_eq_left h2]
        have hm : n < i + (r : ℕ) - ((k : ℕ) - (n - i)) := by
          by_contra hcon
          exact h1 ⟨by omega, by omega⟩
        exact (coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hg hm)).symm
      · rw [ite_eq_right h2]

end Work.WilE4.CAD
