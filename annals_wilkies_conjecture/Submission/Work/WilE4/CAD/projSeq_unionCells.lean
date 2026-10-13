import Mathlib
import Submission.Work.WilE4.CAD.FiberClosureDefs
import Submission.Work.WilE4.CAD.CellsUnion
import Submission.Work.WilE4.CAD.CadCells_isUnionOf

namespace Work.WilE4.CAD

/-- `projSeq` unwinds to its last step: the `(n+1)`-fold iterated projection is always obtained by
applying `downStep k 0` once to a state at level `1`. -/
theorem projSeq_eq_downStep_zero (k : ℕ) : ∀ (n : ℕ) (S : ProjState k (n+1)),
    ∃ M : ProjState k 1, projSeq k (n+1) S = downStep k 0 M := by
  intro n
  induction n with
  | zero =>
    intro S
    exact ⟨S, rfl⟩
  | succ n ih =>
    intro S
    obtain ⟨M, hM⟩ := ih (downStep k (n+1) S)
    exact ⟨M, by rw [projSeq_succ]; exact hM⟩

/-- The iterated projection of a set whose atoms lie in the family `H` is a union of cells of the
decomposition at the final level. -/
theorem projSeq_unionCells (k j : ℕ) (Z : SAd (k+(j+2))) (H : List (MvPolynomial (Fin (k+(j+2))) ℝ))
    (hatoms : ∀ B ∈ Z.basics, ∀ P ∈ B.eqs ++ B.pos, P ∈ H) :
    ∃ L : List (SAd (k+1)), (∀ C ∈ L, C ∈ CadCells (k+1) (projSeq k (j+1) (Z,H)).2) ∧
      (projSeq k (j+1) (Z,H)).1 = unionCells L := by
  obtain ⟨M, hM⟩ := projSeq_eq_downStep_zero k j (Z, H)
  refine ⟨projCells M.2 M.1, ?_, ?_⟩
  · intro C hC
    rw [hM]
    exact (projCells_mem M.2 M.1 C hC).1
  · rw [hM]
    rfl

end Work.WilE4.CAD
