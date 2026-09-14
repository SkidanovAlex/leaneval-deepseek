import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.LinearAlgebra.Matrix.Nonsingular

open Matrix
open scoped BigOperators

set_option autoImplicit false

namespace Commons.LinearAlgebra.Matrix

/-- If an `n × r` integer matrix has an invertible (over `ℤ`, i.e. non-zero
determinant) `r × r` submatrix formed by selecting `r` rows, then its columns are
linearly independent over `ℤ`. -/
theorem cols_linearIndependent_of_exists_submatrix_det_ne_zero
    {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ)
    (h : ∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0) :
    LinearIndependent ℤ A.col := by
  classical
  rcases h with ⟨e, he⟩
  let S : Matrix (Fin r) (Fin r) ℤ := A.submatrix e (fun j : Fin r => j)
  -- The square submatrix `S` has non-zero determinant, hence (as `ℤ` is a domain)
  -- its columns are linearly independent.
  have hS_col : LinearIndependent ℤ S.col := by
    refine Matrix.Nonsingular.linearIndependent_col (A := S) ?_
    rw [Matrix.nonsingular_iff_det_ne_zero]
    exact he
  -- Transfer linear independence from the columns of `S` to those of `A`:
  -- restricting a relation among the columns of `A` to the rows indexed by `e`
  -- gives the same relation among the columns of `S`.
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  rw [Fintype.linearIndependent_iff] at hS_col
  have hsum : (∑ j : Fin r, g j • S.col j) = 0 := by
    funext k0
    have hgk : (∑ j : Fin r, g j • A.col j) (e k0) = 0 := by
      exact congrFun hg (e k0)
    calc
      (∑ j : Fin r, g j • S.col j) k0
          = ∑ j : Fin r, g j * S k0 j := by
            simp [Finset.sum_apply]
      _ = ∑ j : Fin r, g j * A (e k0) j := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [S]
      _ = (∑ j : Fin r, g j • A.col j) (e k0) := by
            simp [Finset.sum_apply]
      _ = 0 := hgk
  exact hS_col g hsum k

end Commons.LinearAlgebra.Matrix