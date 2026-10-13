import Mathlib
import Submission.Work.WilCrux.GR.Defs
import Submission.Work.WilCrux.GR.TrAux
import Submission.Work.WilCrux.GR.IdxStep
import Submission.Work.WilCrux.GR.TrSheet

namespace Work.WilCrux.GR

open Work.WilCrux

theorem Transfer (m N : ℕ) (w' : Fin N → Work.WilCrux.CellType) :
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
          Fin.castSucc (Work.WilCrux.graphIdx w' k)) ∧
    (∀ (z : Fin (m + N + 1) → ℝ) (i : Fin (m + Work.WilCrux.nBand N w')),
        z (Work.WilCrux.selBand m (Fin.snoc w' Work.WilCrux.CellType.graph)
            (Fin.cast (congrArg (Nat.add m) (Work.WilCrux.nBand_snoc_graph N w').symm) i)) =
          Fin.init z (Work.WilCrux.selBand m w' i)) ∧
    (∀ (v : Fin (m + Work.WilCrux.nBand N w') → ℝ)
        (u : Fin (Work.WilCrux.nGraph N w' + 1) → ℝ),
        Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Fin.snoc w' Work.WilCrux.CellType.graph))
            (Work.WilCrux.liftG m N w' v) (Work.WilCrux.liftUg N w' u) =
          Fin.snoc (Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv w') v (Fin.init u))
            (u (Fin.last (Work.WilCrux.nGraph N w')))) ∧
    (∀ (z : Fin (m + N + 1) → ℝ) (i : Fin (m + Work.WilCrux.nBand N w')),
        z (Work.WilCrux.selBand m (Fin.snoc w' Work.WilCrux.CellType.band)
            (Fin.cast (congrArg (Nat.add m) (Work.WilCrux.nBand_snoc_band N w').symm)
              (Fin.castSucc i))) =
          Fin.init z (Work.WilCrux.selBand m w' i)) ∧
    (∀ z : Fin (m + N + 1) → ℝ,
        z (Work.WilCrux.selBand m (Fin.snoc w' Work.WilCrux.CellType.band)
            (Fin.cast (congrArg (Nat.add m) (Work.WilCrux.nBand_snoc_band N w').symm)
              (Fin.last (m + Work.WilCrux.nBand N w')))) = z (Fin.last (m + N))) ∧
    (∀ (v : Fin (m + Work.WilCrux.nBand (N + 1) (Fin.snoc w' Work.WilCrux.CellType.band)) → ℝ)
        (u : Fin (Work.WilCrux.nGraph N w') → ℝ),
        Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Fin.snoc w' Work.WilCrux.CellType.band))
            v (Work.WilCrux.liftUb N w' u) =
          Fin.snoc (Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv w')
            (Work.WilCrux.resB m N w' v) u) (Work.WilCrux.lastB m N w' v)) := by
  -- the six index transfers, and the two sheet-parametrisation transfers
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := IdxStep N w'
  have h8 := Tr.sheet_pt_snoc_graph m N w'
  have h11 := Tr.sheet_pt_snoc_band m N w'
  -- the band projection after appending a graph level: the top level is not a band level
  have h7 : ∀ (z : Fin (m + N + 1) → ℝ) (i : Fin (m + nBand N w')),
      z (selBand m (Fin.snoc w' CellType.graph)
          (Fin.cast (congrArg (Nat.add m) (nBand_snoc_graph N w').symm) i)) =
        Fin.init z (selBand m w' i) := by
    intro z i
    refine Fin.addCases (motive := fun i => z (selBand m (Fin.snoc w' CellType.graph)
        (Fin.cast (congrArg (Nat.add m) (nBand_snoc_graph N w').symm) i)) =
        Fin.init z (selBand m w' i)) ?_ ?_ i
    · intro i₁
      rw [Tr.cast_castAdd (nBand_snoc_graph N w').symm i₁, selBand_castAdd, selBand_castAdd]
      congr 1
    · intro k
      rw [Tr.cast_natAdd (nBand_snoc_graph N w').symm k, selBand_natAdd, selBand_natAdd, h1 k]
      congr 1
  -- the band projection after appending a band level: the old coordinates are unchanged
  have h9 : ∀ (z : Fin (m + N + 1) → ℝ) (i : Fin (m + nBand N w')),
      z (selBand m (Fin.snoc w' CellType.band)
          (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w').symm) (Fin.castSucc i))) =
        Fin.init z (selBand m w' i) := by
    intro z i
    refine Fin.addCases (motive := fun i => z (selBand m (Fin.snoc w' CellType.band)
        (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w').symm) (Fin.castSucc i))) =
        Fin.init z (selBand m w' i)) ?_ ?_ i
    · intro i₁
      rw [Tr.cast_castSucc_castAdd (nBand_snoc_band N w').symm i₁, selBand_castAdd,
        selBand_castAdd]
      congr 1
    · intro k
      rw [Tr.cast_castSucc_natAdd (nBand_snoc_band N w').symm k, selBand_natAdd, selBand_natAdd,
        h4 k]
      congr 1
  -- the new top band coordinate is the last coordinate of `ℝ^{m+N}`
  have h10 : ∀ z : Fin (m + N + 1) → ℝ,
      z (selBand m (Fin.snoc w' CellType.band)
          (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w').symm)
            (Fin.last (m + nBand N w')))) = z (Fin.last (m + N)) := by
    intro z
    rw [Tr.cast_last (nBand_snoc_band N w').symm, selBand_natAdd, h5]
    congr 1
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end Work.WilCrux.GR
