import Mathlib
import Submission.Work.Idx.WPenAppendDefs
import Submission.Work.Idx.wPen_append_entry_facts

namespace Work.Idx

/-- The five elementary block identities of the append step, for the block matrices `Smat`, `Ablk`,
`Bblk`, `Adiag`, `Bdiag`, `Rmat` on the index `WIdx n d ⊕ Fin n = (Fin (d+1) × Fin n) ⊕ Fin n`
(all defined in `Submission/Work/Idx/WPenAppendDefs.lean`). -/
theorem wPen_append_block_ids (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (Work.Idx.Smat X n d * Work.Idx.Ablk X n d
        = Work.Idx.Adiag X n d - Work.Idx.Bdiag X n d b * Work.Idx.Rmat X n d) ∧
    (Work.Idx.Smat X n d * Work.Idx.Bblk X n d b = Work.Idx.Bdiag X n d b) ∧
    (Work.Idx.Adiag X n d * Work.Idx.Rmat X n d = 0) ∧
    (Work.Idx.Rmat X n d * Work.Idx.Rmat X n d = 0) ∧
    (Work.Idx.Smat X n d * Work.Idx.Smat X n d = (1 : Matrix
      (Work.Idx.WIdx n d ⊕ Fin n) (Work.Idx.WIdx n d ⊕ Fin n) C(X, ℂ))) := by
  -- the entry facts relating the sub-blocks `wPenA`, `Ecol`, `Erow`, `BBl`, `rowb`, `wPenB`
  obtain ⟨hAE, hEA, hEE, hAA, hA1, hAB, hEB⟩ := wPen_append_entry_facts X n d b
  have hAneg : Work.KT.Idx.wPenA X n d * (-Work.Idx.Ecol X n d) = 0 := by
    rw [Matrix.mul_neg, hAE, neg_zero]
  have hEneg : Work.Idx.Erow X n d * (-Work.Idx.Ecol X n d) = -1 := by
    rw [Matrix.mul_neg, hEE]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `S * M' = M'' * (1 - z • R)` coefficientwise, in the case `z^0`
    simp only [Work.Idx.Smat, Work.Idx.Ablk, Work.Idx.Adiag, Work.Idx.Bdiag, Work.Idx.Rmat]
    simp only [Matrix.fromBlocks_multiply]
    rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  · -- the `z^1` coefficient of the same identity
    simp only [Work.Idx.Smat, Work.Idx.Bblk, Work.Idx.Bdiag]
    simp only [Matrix.fromBlocks_multiply]
    rw [hAB, hAneg, hEB, hEneg]
    simp
  · simp only [Work.Idx.Adiag, Work.Idx.Rmat]
    simp only [Matrix.fromBlocks_multiply]
    simp
  · simp only [Work.Idx.Rmat]
    simp only [Matrix.fromBlocks_multiply]
    simp
  · simp only [Work.Idx.Smat]
    simp only [Matrix.fromBlocks_multiply]
    rw [hAA, hA1, hAE, hEA, hEE]
    simp

end Work.Idx
