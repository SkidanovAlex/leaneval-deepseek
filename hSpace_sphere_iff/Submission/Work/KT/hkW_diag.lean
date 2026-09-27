import Mathlib
import Submission.Work.KT.hkWDefs

namespace Work.KT

open Matrix

noncomputable section

/-- **The `W`-conjugate of the block diagonal is the diagonal `diag(1_p,0)`.**  If `X` is an
idempotent `p × p` matrix then `Wblk p X * Dblk p X X * Wblk p X` is the diagonal matrix
`diag(1_p, 0)` of size `p+p` (the reindexed block matrix `[[1,0],[0,0]]`). -/
theorem hkW_diag {R : Type} [Ring R] {p : ℕ} {X : Matrix (Fin p) (Fin p) R}
    (hX : X * X = X) :
    Wblk p X * Dblk p X X * Wblk p X
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 0) := by
  -- Write the two block matrices in the `Fin p ⊕ Fin p` indexing.
  set A : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) R :=
    Matrix.fromBlocks X (1 - X) (1 - X) X with hA
  set B : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) R :=
    Matrix.fromBlocks X 0 0 (1 - X) with hB
  -- `Wblk` and `Dblk` are the images of `A` and `B` under the reindexing ring equivalence.
  let ρ : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) R ≃+*
      Matrix (Fin (p + p)) (Fin (p + p)) R :=
    Matrix.reindexRingEquiv R finSumFinEquiv
  have hW : Wblk p X = ρ A := by rw [hA, Wblk]; rfl
  have hD : Dblk p X X = ρ B := by rw [hB, Dblk]; rfl
  -- Consequence of idempotency: the complementary block satisfies `(1-X)*X = X*(1-X) = 0`
  -- and `(1-X)*(1-X) = 1-X` (it is again idempotent, and the two blocks are orthogonal).
  have hYX : (1 - X) * X = 0 := by rw [sub_mul, one_mul, hX, sub_self]
  have hXY : X * (1 - X) = 0 := by rw [mul_sub, mul_one, hX, sub_self]
  have hYY : (1 - X) * (1 - X) = 1 - X := by rw [mul_sub, mul_one, hYX, sub_zero]
  -- Block multiplication: `A * B = [[X, 1-X], [0, 0]]`.
  have hAB : A * B = Matrix.fromBlocks X (1 - X) 0 0 := by
    rw [hA, hB, Matrix.fromBlocks_multiply]
    simp only [hX, hYX, hXY, hYY, mul_zero, add_zero, zero_add]
  -- Block multiplication again: `A * B * A = [[1, 0], [0, 0]]`.
  have hABA : A * B * A = Matrix.fromBlocks 1 0 0 0 := by
    rw [hAB, hA, Matrix.fromBlocks_multiply]
    simp only [hX, hYX, hXY, hYY, zero_mul, add_zero, add_sub_cancel]
  -- Transport along the ring equivalence: a ring hom sends the product to the product.
  rw [hW, hD, ← map_mul, ← map_mul]
  change ρ (A * B * A) = ρ (Matrix.fromBlocks 1 0 0 0)
  exact congrArg ρ hABA

end

end Work.KT
