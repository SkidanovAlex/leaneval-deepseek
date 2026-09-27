import Mathlib
import Submission.Work.KT.Fund.graphProj_block_aux

namespace Work.KT.Fund

/-- The inverse of a unit of `Matrix (Fin (n+k)) (Fin (n+k)) S` that is (via `finSumFinEquiv`)
the block-diagonal matrix `fromBlocks u₁ 0 0 u₂` is the block-diagonal matrix of the inverses. -/
theorem fromBlocks_unit_inv {S : Type} [Ring S] (n k : ℕ)
    (u : (Matrix (Fin (n + k)) (Fin (n + k)) S)ˣ)
    (u₁ : (Matrix (Fin n) (Fin n) S)ˣ) (u₂ : (Matrix (Fin k) (Fin k) S)ˣ)
    (h : (u : Matrix (Fin (n + k)) (Fin (n + k)) S)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (u₁ : Matrix (Fin n) (Fin n) S) 0 0
            (u₂ : Matrix (Fin k) (Fin k) S))) :
    ((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) S)ˣ) : Matrix (Fin (n + k)) (Fin (n + k)) S)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks ((u₁⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S)
            0 0 ((u₂⁻¹ : (Matrix (Fin k) (Fin k) S)ˣ) : Matrix (Fin k) (Fin k) S)) := by
  -- `B * A = 1` for the two block-diagonal matrices, from the block multiplication rule.
  have hBA :
      Matrix.fromBlocks ((u₁⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S)
          (0 : Matrix (Fin n) (Fin k) S) (0 : Matrix (Fin k) (Fin n) S)
          ((u₂⁻¹ : (Matrix (Fin k) (Fin k) S)ˣ) : Matrix (Fin k) (Fin k) S)
        * Matrix.fromBlocks (u₁ : Matrix (Fin n) (Fin n) S) (0 : Matrix (Fin n) (Fin k) S)
          (0 : Matrix (Fin k) (Fin n) S) (u₂ : Matrix (Fin k) (Fin k) S)
        = 1 := by
    rw [Matrix.fromBlocks_multiply]; simp
  -- `reindex`isation of the block matrix is `u`.
  have hφA :
      (Matrix.reindexLinearEquiv S S finSumFinEquiv finSumFinEquiv)
          (Matrix.fromBlocks (u₁ : Matrix (Fin n) (Fin n) S) 0 0
            (u₂ : Matrix (Fin k) (Fin k) S))
        = (u : Matrix (Fin (n + k)) (Fin (n + k)) S) := by
    rw [Matrix.coe_reindexLinearEquiv]; exact h.symm
  -- `reindexLinearEquiv` is multiplicative and unital, so carries `B * A = 1` to `1`.
  have hBA' :
      (Matrix.reindexLinearEquiv S S finSumFinEquiv finSumFinEquiv)
          (Matrix.fromBlocks ((u₁⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) 0 0
            ((u₂⁻¹ : (Matrix (Fin k) (Fin k) S)ˣ) : Matrix (Fin k) (Fin k) S))
        * (Matrix.reindexLinearEquiv S S finSumFinEquiv finSumFinEquiv)
          (Matrix.fromBlocks (u₁ : Matrix (Fin n) (Fin n) S) 0 0
            (u₂ : Matrix (Fin k) (Fin k) S))
        = 1 := by
    rw [Matrix.reindexLinearEquiv_mul]
    rw [hBA]
    exact Matrix.reindexLinearEquiv_one S S finSumFinEquiv
  -- the right-inverse relation for `u`.
  have hac :
      (Matrix.reindexLinearEquiv S S finSumFinEquiv finSumFinEquiv)
          (Matrix.fromBlocks (u₁ : Matrix (Fin n) (Fin n) S) 0 0
            (u₂ : Matrix (Fin k) (Fin k) S))
        * ((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) S)ˣ) :
            Matrix (Fin (n + k)) (Fin (n + k)) S)
        = 1 := by
    rw [hφA, Units.mul_inv]
  -- in a monoid, a left inverse and a right inverse coincide.
  have key := left_inv_eq_right_inv hBA' hac
  calc ((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) S)ˣ) :
          Matrix (Fin (n + k)) (Fin (n + k)) S)
      = (Matrix.reindexLinearEquiv S S finSumFinEquiv finSumFinEquiv)
          (Matrix.fromBlocks ((u₁⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) 0 0
            ((u₂⁻¹ : (Matrix (Fin k) (Fin k) S)ˣ) : Matrix (Fin k) (Fin k) S)) := key.symm
    _ = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks ((u₁⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) 0 0
            ((u₂⁻¹ : (Matrix (Fin k) (Fin k) S)ˣ) : Matrix (Fin k) (Fin k) S)) := by
        rw [Matrix.coe_reindexLinearEquiv]

end Work.KT.Fund
