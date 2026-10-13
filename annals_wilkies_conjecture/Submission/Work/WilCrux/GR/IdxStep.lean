import Mathlib
import Submission.Work.WilCrux.GR.Defs
import Submission.Work.WilCrux.GR.TrAux

namespace Work.WilCrux.GR

open Work.WilCrux

/-!
## 10. Index bookkeeping for the word obtained by appending one level

`bandIdx w` (resp. `graphIdx w`) is the increasing enumeration of the band (resp. graph)
levels of the type word `w`.  Appending one level on top of `w'` with `Fin.snoc` keeps the old
levels in place (they are shifted by `Fin.castSucc`) and, when the new level is a band / graph,
adds one new level at the very top (`Fin.last N`).

The two ingredients are already available in this workspace:

* `GR.Tr.bandIdx_eq_iff` / `GR.Tr.graphIdx_eq_iff` characterise `bandIdx w k = j` by the two
  conditions `bandBit (w j) = 1` and `bandRank w j = k` (and similarly for graphs);
* `GR.bandRank_snoc_castSucc`, `GR.graphRank_snoc_castSucc`, `GR.bandRank_snoc_last`,
  `GR.graphRank_snoc_last` describe how the ranks transform under `Fin.snoc`.

So each of the six identities below is a two-line verification: membership in the relevant list
of levels, and the value of the rank.
-/

/-- Appending a graph level on top keeps the band level of index `k` where it is. -/
theorem bandIdx_snoc_graph (N : ℕ) (w' : Fin N → CellType) (k : Fin (nBand N w')) :
    bandIdx (Fin.snoc w' CellType.graph) (Fin.cast (nBand_snoc_graph N w').symm k) =
      Fin.castSucc (bandIdx w' k) := by
  rw [Tr.bandIdx_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Fin.snoc_castSucc]
    exact bandIdx_band w' k
  · rw [bandRank_snoc_castSucc N w' CellType.graph, bandRank_bandIdx]
    rfl

/-- Appending a graph level on top keeps the graph level of index `k` where it is. -/
theorem graphIdx_snoc_graph (N : ℕ) (w' : Fin N → CellType) (k : Fin (nGraph N w')) :
    graphIdx (Fin.snoc w' CellType.graph)
        (Fin.cast (nGraph_snoc_graph N w').symm (Fin.castSucc k)) =
      Fin.castSucc (graphIdx w' k) := by
  rw [Tr.graphIdx_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Fin.snoc_castSucc]
    exact graphIdx_graph w' k
  · rw [graphRank_snoc_castSucc N w' CellType.graph, graphRank_graphIdx]
    rfl

/-- The new graph level of `Fin.snoc w' graph` is the last coordinate. -/
theorem graphIdx_snoc_graph_last (N : ℕ) (w' : Fin N → CellType) :
    graphIdx (Fin.snoc w' CellType.graph)
        (Fin.cast (nGraph_snoc_graph N w').symm (Fin.last (nGraph N w'))) = Fin.last N := by
  rw [Tr.graphIdx_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Fin.snoc_last]
    rfl
  · rw [graphRank_snoc_last N w' CellType.graph]
    rfl

/-- Appending a band level on top keeps the band level of index `k` where it is. -/
theorem bandIdx_snoc_band (N : ℕ) (w' : Fin N → CellType) (k : Fin (nBand N w')) :
    bandIdx (Fin.snoc w' CellType.band)
        (Fin.cast (nBand_snoc_band N w').symm (Fin.castSucc k)) =
      Fin.castSucc (bandIdx w' k) := by
  rw [Tr.bandIdx_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Fin.snoc_castSucc]
    exact bandIdx_band w' k
  · rw [bandRank_snoc_castSucc N w' CellType.band, bandRank_bandIdx]
    rfl

/-- The new band level of `Fin.snoc w' band` is the last coordinate. -/
theorem bandIdx_snoc_band_last (N : ℕ) (w' : Fin N → CellType) :
    bandIdx (Fin.snoc w' CellType.band)
        (Fin.cast (nBand_snoc_band N w').symm (Fin.last (nBand N w'))) = Fin.last N := by
  rw [Tr.bandIdx_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Fin.snoc_last]
    rfl
  · rw [bandRank_snoc_last N w' CellType.band]
    rfl

/-- Appending a band level on top keeps the graph level of index `k` where it is. -/
theorem graphIdx_snoc_band (N : ℕ) (w' : Fin N → CellType) (k : Fin (nGraph N w')) :
    graphIdx (Fin.snoc w' CellType.band) (Fin.cast (nGraph_snoc_band N w').symm k) =
      Fin.castSucc (graphIdx w' k) := by
  rw [Tr.graphIdx_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Fin.snoc_castSucc]
    exact graphIdx_graph w' k
  · rw [graphRank_snoc_castSucc N w' CellType.band, graphRank_graphIdx]
    rfl

theorem IdxStep (N : ℕ) (w' : Fin N → Work.WilCrux.CellType) :
    (∀ k : Fin (Work.WilCrux.nBand N w'),
        Work.WilCrux.bandIdx (Fin.snoc w' Work.WilCrux.CellType.graph)
            (Fin.cast (Work.WilCrux.nBand_snoc_graph N w').symm k) =
          Fin.castSucc (Work.WilCrux.bandIdx w' k)) ∧
    (∀ k : Fin (Work.WilCrux.nGraph N w'),
        Work.WilCrux.graphIdx (Fin.snoc w' Work.WilCrux.CellType.graph)
            (Fin.cast (Work.WilCrux.nGraph_snoc_graph N w').symm (Fin.castSucc k)) =
          Fin.castSucc (Work.WilCrux.graphIdx w' k)) ∧
    (Work.WilCrux.graphIdx (Fin.snoc w' Work.WilCrux.CellType.graph)
        (Fin.cast (Work.WilCrux.nGraph_snoc_graph N w').symm
          (Fin.last (Work.WilCrux.nGraph N w'))) = Fin.last N) ∧
    (∀ k : Fin (Work.WilCrux.nBand N w'),
        Work.WilCrux.bandIdx (Fin.snoc w' Work.WilCrux.CellType.band)
            (Fin.cast (Work.WilCrux.nBand_snoc_band N w').symm (Fin.castSucc k)) =
          Fin.castSucc (Work.WilCrux.bandIdx w' k)) ∧
    (Work.WilCrux.bandIdx (Fin.snoc w' Work.WilCrux.CellType.band)
        (Fin.cast (Work.WilCrux.nBand_snoc_band N w').symm
          (Fin.last (Work.WilCrux.nBand N w'))) = Fin.last N) ∧
    (∀ k : Fin (Work.WilCrux.nGraph N w'),
        Work.WilCrux.graphIdx (Fin.snoc w' Work.WilCrux.CellType.band)
            (Fin.cast (Work.WilCrux.nGraph_snoc_band N w').symm k) =
          Fin.castSucc (Work.WilCrux.graphIdx w' k)) :=
  ⟨bandIdx_snoc_graph N w', graphIdx_snoc_graph N w', graphIdx_snoc_graph_last N w',
   bandIdx_snoc_band N w', bandIdx_snoc_band_last N w', graphIdx_snoc_band N w'⟩

end Work.WilCrux.GR
