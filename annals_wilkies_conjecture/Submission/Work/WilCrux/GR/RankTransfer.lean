import Mathlib
import Submission.Work.WilCrux.GR.Defs

namespace Work.WilCrux.GR

open Work.WilCrux

/-! ## Rank transfer along `Fin.snoc`

`bandRank w j` (resp. `graphRank w j`) counts the band (resp. graph) levels of the type word `w`
that lie strictly below the index `j`.  Appending one level on top with `Fin.snoc` does not change
these counts below an old index, and the count at the new last index is the total number of band
(resp. graph) levels of the old word, `nBand`/`nGraph`.
-/

/-- Appending a level on top does not change the number of band levels below an old index. -/
theorem bandRank_snoc_castSucc (N : ℕ) (w' : Fin N → CellType) (t : CellType) (j : Fin N) :
    bandRank (Fin.snoc w' t) (Fin.castSucc j) = bandRank w' j := by
  rw [bandRank, bandRank, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  have hlast : ¬ (Fin.last N < Fin.castSucc j ∧
      bandBit ((Fin.snoc w' t : Fin (N + 1) → CellType) (Fin.last N)) = 1) :=
    fun h => absurd (lt_trans h.1 (Fin.castSucc_lt_last j)) (lt_irrefl _)
  rw [ite_eq_right hlast, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.snoc_castSucc]

/-- Appending a level on top does not change the number of graph levels below an old index. -/
theorem graphRank_snoc_castSucc (N : ℕ) (w' : Fin N → CellType) (t : CellType) (j : Fin N) :
    graphRank (Fin.snoc w' t) (Fin.castSucc j) = graphRank w' j := by
  rw [graphRank, graphRank, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  have hlast : ¬ (Fin.last N < Fin.castSucc j ∧
      graphBit ((Fin.snoc w' t : Fin (N + 1) → CellType) (Fin.last N)) = 1) :=
    fun h => absurd (lt_trans h.1 (Fin.castSucc_lt_last j)) (lt_irrefl _)
  rw [ite_eq_right hlast, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.snoc_castSucc]

/-- The number of band levels below the new last index is the total number of band levels of the
old word. -/
theorem bandRank_snoc_last (N : ℕ) (w' : Fin N → CellType) (t : CellType) :
    bandRank (Fin.snoc w' t) (Fin.last N) = nBand N w' := by
  rw [bandRank, Finset.card_filter, Fin.sum_univ_castSucc]
  rw [show (if (Fin.last N < Fin.last N ∧
      bandBit ((Fin.snoc w' t : Fin (N + 1) → CellType) (Fin.last N)) = 1) then (1 : ℕ) else 0) = 0
      from by simp]
  rw [add_zero, nBand_eq_card, Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Fin.castSucc_lt_last, Fin.snoc_castSucc]

/-- The number of graph levels below the new last index is the total number of graph levels of the
old word. -/
theorem graphRank_snoc_last (N : ℕ) (w' : Fin N → CellType) (t : CellType) :
    graphRank (Fin.snoc w' t) (Fin.last N) = nGraph N w' := by
  rw [graphRank, Finset.card_filter, Fin.sum_univ_castSucc]
  rw [show (if (Fin.last N < Fin.last N ∧
      graphBit ((Fin.snoc w' t : Fin (N + 1) → CellType) (Fin.last N)) = 1) then (1 : ℕ) else 0) = 0
      from by simp]
  rw [add_zero, nGraph_eq_card, Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Fin.castSucc_lt_last, Fin.snoc_castSucc]

theorem RankTransfer (N : ℕ) (w' : Fin N → Work.WilCrux.CellType) :
    (∀ (t : Work.WilCrux.CellType) (j : Fin N),
        Work.WilCrux.bandRank (Fin.snoc w' t) (Fin.castSucc j) = Work.WilCrux.bandRank w' j) ∧
    (∀ (t : Work.WilCrux.CellType) (j : Fin N),
        Work.WilCrux.graphRank (Fin.snoc w' t) (Fin.castSucc j) = Work.WilCrux.graphRank w' j) ∧
    (Work.WilCrux.bandRank (Fin.snoc w' Work.WilCrux.CellType.band) (Fin.last N) = Work.WilCrux.nBand N w') ∧
    (Work.WilCrux.bandRank (Fin.snoc w' Work.WilCrux.CellType.graph) (Fin.last N) = Work.WilCrux.nBand N w') ∧
    (Work.WilCrux.graphRank (Fin.snoc w' Work.WilCrux.CellType.graph) (Fin.last N) = Work.WilCrux.nGraph N w') ∧
    (Work.WilCrux.graphRank (Fin.snoc w' Work.WilCrux.CellType.band) (Fin.last N) = Work.WilCrux.nGraph N w') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t j => bandRank_snoc_castSucc N w' t j
  · exact fun t j => graphRank_snoc_castSucc N w' t j
  · exact bandRank_snoc_last N w' CellType.band
  · exact bandRank_snoc_last N w' CellType.graph
  · exact graphRank_snoc_last N w' CellType.graph
  · exact graphRank_snoc_last N w' CellType.band

end Work.WilCrux.GR
