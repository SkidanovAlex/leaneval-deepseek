import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic

namespace Work.KT

open Matrix

theorem sum_mvN_congr :
    ∀ (R : Type) [Ring R] (p p' q q' : Mat R),
      Mat.MvN p p' → Mat.MvN q q' → Mat.MvN (p.sum q) (p'.sum q') := by
  intro R _ p p' q q' hp hq
  obtain ⟨a, b, hba, hab⟩ := hp
  obtain ⟨c, d, hdc, hcd⟩ := hq
  refine ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a 0 0 c),
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks b 0 0 d), ?_, ?_⟩
  · change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks b 0 0 d) *
        Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a 0 0 c) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.2 0 0 q.2)
    rw [reindexMul, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hba, hdc]
  · change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a 0 0 c) *
        Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks b 0 0 d) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p'.2 0 0 q'.2)
    rw [reindexMul, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hab, hcd]

end Work.KT
