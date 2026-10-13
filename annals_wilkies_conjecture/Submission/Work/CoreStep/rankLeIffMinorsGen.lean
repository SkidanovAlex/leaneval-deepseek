import Mathlib
import Submission.Work.WilE4.CAD.rank_le_of_minors_det_eq_zero

/-!
# Rank ≤ `k` versus vanishing of all `(k+1) × (k+1)` minors

For a real matrix `A : Matrix ι (Fin N) ℝ` with `ι` finite, `A.rank ≤ k` if and only if every
`(k+1) × (k+1)` minor of `A` vanishes.

* If `A.rank ≤ k`, then for any row and column selections `σ`, `τ` the submatrix
  `A.submatrix σ τ` has rank `≤ A.rank ≤ k` (`Matrix.rank_submatrix_le`); a square matrix with
  non-zero determinant has rank equal to its size (`Matrix.rank_of_det_ne_zero`), so its
  determinant must vanish.
* Conversely, if `A.rank ≥ k+1` then the rows span a space of dimension `≥ k+1`, so `k+1` of
  them are linearly independent; the resulting `(k+1) × N` matrix `B` has rank `k+1`, so its
  columns span a `(k+1)`-dimensional space and `k+1` of them are linearly independent. The
  corresponding square submatrix has linearly independent columns, hence non-zero determinant.

The extraction of independent members of a spanning family is
`Work.WilE4.CAD.exists_linearIndependent_comp_of_le_finrank`.
-/

namespace Work.CoreStep

open Matrix

/-- A real matrix (with finite row index type) has rank at most `k` if and only if all of its
`(k+1) × (k+1)` minors vanish. -/
theorem rankLeIffMinorsGen {ι : Type*} [Fintype ι] {N k : ℕ} (A : Matrix ι (Fin N) ℝ) :
    A.rank ≤ k ↔
      ∀ (σ : Fin (k + 1) ↪ ι) (τ : Fin (k + 1) ↪ Fin N), (A.submatrix σ τ).det = 0 := by
  constructor
  · intro h σ τ
    by_contra hdet
    have h1 : (A.submatrix σ τ).rank = k + 1 := by
      simpa using Matrix.rank_of_det_ne_zero hdet
    have h2 : (A.submatrix σ τ).rank ≤ A.rank :=
      Matrix.rank_submatrix_le A (σ : Fin (k + 1) → ι) (τ : Fin (k + 1) → Fin N)
    omega
  · intro hmin
    by_contra hlt
    have hk : k + 1 ≤ A.rank := by omega
    -- `k + 1` linearly independent rows of `A`
    obtain ⟨r, hr⟩ :=
      Work.WilE4.CAD.exists_linearIndependent_comp_of_le_finrank (K := ℝ) A.row (n := k + 1)
        (by rw [← Matrix.rank_eq_finrank_span_row A]; exact hk)
    have hrinj : Function.Injective r := hr.injective.of_comp
    set B : Matrix (Fin (k + 1)) (Fin N) ℝ := A.submatrix r id with hB
    have hBrow : LinearIndependent ℝ B.row := by
      rw [hB]
      have hrow : (A.submatrix r id).row = A.row ∘ r := by ext j i; rfl
      rw [hrow]
      exact hr
    have hBrank : B.rank = k + 1 := by
      rw [LinearIndependent.rank_matrix hBrow]
      simp
    -- `k + 1` linearly independent columns of `B`
    obtain ⟨c, hc⟩ :=
      Work.WilE4.CAD.exists_linearIndependent_comp_of_le_finrank (K := ℝ) B.col (n := k + 1)
        (by rw [← Matrix.rank_eq_finrank_span_cols B]; exact hBrank.ge)
    have hcinj : Function.Injective c := hc.injective.of_comp
    have hcol : (B.submatrix id c).col = B.col ∘ c := by
      funext j i
      rfl
    have hScol : LinearIndependent ℝ (B.submatrix id c).col := by rw [hcol]; exact hc
    have hdet : (B.submatrix id c).det ≠ 0 :=
      Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_col hScol)
    have hCeq : B.submatrix id c = A.submatrix r c := by
      rw [hB, Matrix.submatrix_submatrix]
      rfl
    rw [hCeq] at hdet
    exact hdet (hmin ⟨r, hrinj⟩ ⟨c, hcinj⟩)

end Work.CoreStep
