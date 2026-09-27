import Mathlib
import Submission.Work.KT.K0_prod_defs
import Submission.Work.KT.Basic

/-!
# `Work.KT.K0prod.mvN_zero_sum` — the two diagonal embeddings differ by a block swap

For an idempotent `r : Mat R`, padding `r` by a zero block on the left and on the right gives
Murray–von Neumann equivalent idempotents:
`0 ⊕ r ~ r ⊕ 0`.  The equivalence is implemented by the block-swap matrix
`Y = fromBlocks 0 1 1 0`, which is an involution and exchanges the two blocks.
-/

namespace Work.KT.K0prod

open _root_.Matrix

variable {R : Type} [Ring R]

/-- **Block swap.**  Swapping the two blocks of the idempotent `M` padded by a zero block (in
either order). -/
lemma mvN_sum_zero_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (hM : M * M = M) :
    Mat.MvN (Mat.sum (zeroMat R n) ⟨n, M⟩) (Mat.sum ⟨n, M⟩ (zeroMat R n)) := by
  change Mat.MvN
    ⟨n + n, Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 0 0 M)⟩
    ⟨n + n, Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 0)⟩
  set X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := Matrix.fromBlocks 0 0 0 M with hX
  set Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := Matrix.fromBlocks 0 1 1 0 with hY
  set Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := Matrix.fromBlocks M 0 0 0 with hZ
  have hXX : X * X = X := by
    rw [hX, Matrix.fromBlocks_multiply]
    simp [hM]
  have hYY : Y * Y = 1 := by
    rw [hY, Matrix.fromBlocks_multiply]
    simp
  have hYXY : Y * X * Y = Z := by
    rw [hY, hX, hZ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have h1 : (X * Y) * (Y * X) = X := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y Y X, hYY, Matrix.one_mul, hXX]
  have h2 : (Y * X) * (X * Y) = Z := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc X X Y, hXX, ← Matrix.mul_assoc Y X Y, hYXY]
  have hri : ∀ A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R,
      Matrix.reindex finSumFinEquiv finSumFinEquiv A *
        Matrix.reindex finSumFinEquiv finSumFinEquiv B =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (A * B) :=
    fun A B => reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv A B
  refine ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv (Y * X),
    Matrix.reindex finSumFinEquiv finSumFinEquiv (X * Y), ?_, ?_⟩
  · rw [hri (X * Y) (Y * X), h1]
  · rw [hri (Y * X) (X * Y), h2]

lemma mvN_zero_sum {R : Type} [Ring R] (r : Mat R) (hr : r.IsIdem) :
    Mat.MvN (Mat.sum (zeroMat R r.1) r) (Mat.sum r (zeroMat R r.1)) := by
  obtain ⟨n, M⟩ := r
  exact mvN_sum_zero_aux M hr

end Work.KT.K0prod
