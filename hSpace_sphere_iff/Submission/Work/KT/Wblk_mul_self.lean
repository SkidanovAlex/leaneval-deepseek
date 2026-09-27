import Mathlib
import Submission.Work.KT.hkWDefs

namespace Work.KT

open Matrix

noncomputable section

/-- Reindexing the identity matrix along `finSumFinEquiv` returns the identity. -/
private lemma Wblk_reindex_one' {R : Type} [Ring R] {p : ℕ} :
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (1 : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) R) = 1 := by
  rw [Matrix.reindex_apply]
  exact Matrix.submatrix_one_equiv finSumFinEquiv.symm

theorem Wblk_mul_self {R : Type} [Ring R] {p : ℕ} {C : Matrix (Fin p) (Fin p) R}
    (hC : C * C = C) : Wblk p C * Wblk p C = 1 := by
  have hY : (1 - C) * C = 0 := by rw [sub_mul, one_mul, hC, sub_self]
  have hZ : C * (1 - C) = 0 := by rw [mul_sub, mul_one, hC, sub_self]
  have hW : (1 - C) * (1 - C) = 1 - C := by rw [mul_sub, mul_one, hY, sub_zero]
  have hA : Matrix.fromBlocks C (1 - C) (1 - C) C * Matrix.fromBlocks C (1 - C) (1 - C) C
      = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show C * C + (1 - C) * (1 - C) = 1
      rw [hC, hW]; abel
    · show C * (1 - C) + (1 - C) * C = 0
      rw [hZ, hY]; abel
    · show (1 - C) * C + C * (1 - C) = 0
      rw [hY, hZ]; abel
    · show (1 - C) * (1 - C) + C * C = 1
      rw [hW, hC]; abel
  show Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks C (1 - C) (1 - C) C)
      * Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks C (1 - C) (1 - C) C) = 1
  rw [reindexMul, hA, Wblk_reindex_one']

end

end Work.KT
