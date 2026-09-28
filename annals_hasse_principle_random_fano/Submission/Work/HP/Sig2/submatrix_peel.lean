import Mathlib
import Submission.Work.HP.Sig2.PeelDefs

namespace Work.HP.Sig2

open Matrix

/-- Peeling the head index `0` off a matrix indexed by `Fin (R+1)`: reindexing by
`peelEquiv R : Fin R ⊕ Fin 1 ≃ Fin (R+1)` turns `G` into the `2 × 2` block matrix whose
leading block is the tail `pTail G`, whose off-diagonal blocks are the first-row tail
`pVec G`, and whose trailing `1 × 1` block is the head `pHead G`.  Symmetry of `G`
(available since `G` is positive definite) is used for the off-diagonal blocks. -/
theorem submatrix_peel {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef) :
    G.submatrix (peelEquiv R) (peelEquiv R) =
      Matrix.fromBlocks (pTail G)
        (Matrix.of (fun i (_ : Fin 1) => pVec G i))
        (Matrix.of (fun (_ : Fin 1) j => pVec G j))
        (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => pHead G)) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · simp [submatrix_apply, pTail]
  · simp only [submatrix_apply, fromBlocks_apply₁₂, Matrix.of_apply, peelEquiv_inl, peelEquiv_inr,
      pVec]
    exact (hG.isHermitian.apply i.succ 0).symm
  · simp only [submatrix_apply, fromBlocks_apply₂₁, Matrix.of_apply, peelEquiv_inl, peelEquiv_inr,
      pVec]
  · simp only [submatrix_apply, fromBlocks_apply₂₂, Matrix.of_apply, peelEquiv_inr, pHead]

end Work.HP.Sig2
