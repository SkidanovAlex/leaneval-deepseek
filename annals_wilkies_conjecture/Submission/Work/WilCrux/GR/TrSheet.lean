/-
  The sheet parametrisation after appending one level: the graph case and the band case.

  `sheetPtM (wordEquiv (Fin.snoc w' t)) ...` is obtained from the sheet parametrisation of `w'`
  by appending the new top coordinate: for `t = graph` the band coordinates are unchanged (via
  `liftG`) and the new graph coordinate is the last entry of `u` (via `liftUg`); for `t = band`
  the graph coordinates are unchanged (via `liftUb`) and the band coordinates are split into the
  old ones (`resB`) and the new last one (`lastB`).

  Proved pointwise from `sheetPt_wordEquiv_band`/`sheetPt_wordEquiv_graph` (which say that the
  `j`-th fibre coordinate of a sheet point is the `bandRank`-th band coordinate or the
  `graphRank`-th graph coordinate of the level `j`) together with the rank transfers
  `GR.bandRank_snoc_castSucc` etc.

  Everything is `sorry`-free and rests only on `propext`, `Quot.sound` and `Classical.choice`.
-/
import Mathlib
import Submission.Work.WilCrux.GR.Defs
import Submission.Work.WilCrux.GR.TrAux

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux.GR.Tr

open Work.WilCrux

theorem sheet_pt_snoc_graph (m N : ℕ) (w' : Fin N → CellType)
    (v : Fin (m + nBand N w') → ℝ) (u : Fin (nGraph N w' + 1) → ℝ) :
    sheetPtM (wordEquiv (Fin.snoc w' CellType.graph)) (liftG m N w' v) (liftUg N w' u) =
      Fin.snoc (sheetPtM (wordEquiv w') v (Fin.init u)) (u (Fin.last (nGraph N w'))) := by
  funext x
  rcases Fin.eq_castSucc_or_eq_last x with ⟨y, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    refine Fin.addCases (motive := fun y => sheetPtM (wordEquiv (Fin.snoc w' CellType.graph))
        (liftG m N w' v) (liftUg N w' u) (Fin.castSucc y) =
        (sheetPtM (wordEquiv w') v (Fin.init u)) y) ?_ ?_ y
    · intro i
      rw [Tr.castSucc_castAdd (n := N) i, sheetPtM_castAdd]
      simp only [liftG]
      rw [Tr.cast_castAdd (nBand_snoc_graph N w') i, sheetPtM_castAdd]
    · intro j
      rw [← Fin.natAdd_castSucc]
      by_cases hb : bandBit ((Fin.snoc w' CellType.graph : Fin (N + 1) → CellType)
        (Fin.castSucc j)) = 1
      · have hbj : bandBit (w' j) = 1 := by simpa [Fin.snoc_castSucc] using hb
        rw [sheetPt_wordEquiv_band (Fin.snoc w' CellType.graph) (liftG m N w' v) (liftUg N w' u)
              (Fin.castSucc j) hb,
          sheetPt_wordEquiv_band w' v (Fin.init u) j hbj]
        simp only [liftG]
        rw [Tr.cast_natAdd (nBand_snoc_graph N w')
          ⟨bandRank (Fin.snoc w' CellType.graph) (Fin.castSucc j), _⟩]
        congr 1
        apply Fin.ext
        simp only [Fin.val_natAdd, Fin.val_cast, Fin.val_mk, GR.bandRank_snoc_castSucc]
      · have hbj : bandBit (w' j) = 0 := by
          cases h : w' j <;> simp_all [bandBit, Fin.snoc_castSucc]
        rw [sheetPt_wordEquiv_graph (Fin.snoc w' CellType.graph) (liftG m N w' v) (liftUg N w' u)
              (Fin.castSucc j) (by rw [Fin.snoc_castSucc]; exact hbj),
          sheetPt_wordEquiv_graph w' v (Fin.init u) j hbj]
        simp only [liftUg, Fin.init]
        congr 1
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_mk, GR.graphRank_snoc_castSucc, Fin.val_castSucc]
  · rw [Fin.snoc_last]
    show sheetPtM (wordEquiv (Fin.snoc w' CellType.graph)) (liftG m N w' v) (liftUg N w' u)
        (Fin.natAdd m (Fin.last N)) = u (Fin.last (nGraph N w'))
    rw [sheetPt_wordEquiv_graph (Fin.snoc w' CellType.graph) (liftG m N w' v) (liftUg N w' u)
        (Fin.last N) (by rw [Fin.snoc_last]; rfl)]
    simp only [liftUg]
    congr 1
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_mk, GR.graphRank_snoc_last, Fin.val_last]

theorem sheet_pt_snoc_band (m N : ℕ) (w' : Fin N → CellType)
    (v : Fin (m + nBand (N + 1) (Fin.snoc w' CellType.band)) → ℝ) (u : Fin (nGraph N w') → ℝ) :
    sheetPtM (wordEquiv (Fin.snoc w' CellType.band)) v (liftUb N w' u) =
      Fin.snoc (sheetPtM (wordEquiv w') (resB m N w' v) u) (lastB m N w' v) := by
  funext x
  rcases Fin.eq_castSucc_or_eq_last x with ⟨y, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    refine Fin.addCases (motive := fun y => sheetPtM (wordEquiv (Fin.snoc w' CellType.band))
        v (liftUb N w' u) (Fin.castSucc y) =
        (sheetPtM (wordEquiv w') (resB m N w' v) u) y) ?_ ?_ y
    · intro i
      rw [Tr.castSucc_castAdd (n := N) i, sheetPtM_castAdd, sheetPtM_castAdd]
      simp only [resB]
      exact congrArg v (Tr.cast_castSucc_castAdd (nBand_snoc_band N w').symm i).symm
    · intro j
      rw [← Fin.natAdd_castSucc]
      by_cases hb : bandBit ((Fin.snoc w' CellType.band : Fin (N + 1) → CellType)
        (Fin.castSucc j)) = 1
      · have hbj : bandBit (w' j) = 1 := by simpa [Fin.snoc_castSucc] using hb
        rw [sheetPt_wordEquiv_band (Fin.snoc w' CellType.band) v (liftUb N w' u)
              (Fin.castSucc j) hb,
          sheetPt_wordEquiv_band w' (resB m N w' v) u j hbj]
        simp only [resB]
        rw [← Fin.natAdd_castSucc, Tr.cast_natAdd (nBand_snoc_band N w').symm
          (Fin.castSucc ⟨bandRank w' j, _⟩)]
        congr 1
        apply Fin.ext
        simp only [Fin.val_natAdd, Fin.val_cast, Fin.val_mk, Fin.val_castSucc,
          GR.bandRank_snoc_castSucc]
      · have hbj : bandBit (w' j) = 0 := by
          cases h : w' j <;> simp_all [bandBit, Fin.snoc_castSucc]
        rw [sheetPt_wordEquiv_graph (Fin.snoc w' CellType.band) v (liftUb N w' u)
              (Fin.castSucc j) (by rw [Fin.snoc_castSucc]; exact hbj),
          sheetPt_wordEquiv_graph w' (resB m N w' v) u j hbj]
        simp only [liftUb, Fin.init]
        congr 1
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_mk, GR.graphRank_snoc_castSucc, Fin.val_castSucc]
  · rw [Fin.snoc_last]
    show sheetPtM (wordEquiv (Fin.snoc w' CellType.band)) v (liftUb N w' u)
        (Fin.natAdd m (Fin.last N)) = lastB m N w' v
    rw [sheetPt_wordEquiv_band (Fin.snoc w' CellType.band) v (liftUb N w' u)
        (Fin.last N) (by rw [Fin.snoc_last]; rfl)]
    simp only [lastB]
    rw [Tr.cast_last (nBand_snoc_band N w').symm]
    congr 1
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_cast, Fin.val_mk, Fin.val_last, GR.bandRank_snoc_last]

end Work.WilCrux.GR.Tr
