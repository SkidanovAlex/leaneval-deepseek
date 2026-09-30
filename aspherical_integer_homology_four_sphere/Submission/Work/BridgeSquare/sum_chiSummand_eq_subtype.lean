import Mathlib
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.BridgeSquare

theorem sum_chiSummand_eq_subtype (n : ℕ) (hn : n < 5)
    (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    (∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
        Work.BridgeSquare.chiSummand n hn e s)
      = ∑ s : {s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n //
            s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e},
          Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s.1 •
            Work.BridgeSquare.singGen (Work.MbarHomology.Mbar.chi n
              (Work.MbarHomology.Mbar.rootSimplex n hn e s.1)) := by
  -- `chiSummand` vanishes off the root face, so the sum over all simplices is the sum over the
  -- subtype of simplices whose last vertex is the root cell `e`.  The two `•`-occurrences
  -- (the `ℤ`-module action of `ModuleCat` carried by `chiSummand`, and the canonical one in the
  -- statement) are identified by `Int.cast_smul_eq_zsmul`.
  have hfun : ∀ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
      Work.BridgeSquare.chiSummand n hn e s =
      (if s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e then
        Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s •
          Work.BridgeSquare.singGen (Work.MbarHomology.Mbar.chi n
            (Work.MbarHomology.Mbar.rootSimplex n hn e s)) else 0) := by
    intro s
    by_cases h : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e
    · rw [Work.BridgeSquare.chiSummand_pos n hn e s h, if_pos h]
      rw [← Int.cast_smul_eq_zsmul ℤ]
      simp
    · rw [Work.BridgeSquare.chiSummand_neg n hn e s h, if_neg h]
  simp only [hfun]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (Finset.univ.filter (fun s => s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e))
    (fun _ => by simp)
    (fun s => Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s •
      Work.BridgeSquare.singGen (Work.MbarHomology.Mbar.chi n
        (Work.MbarHomology.Mbar.rootSimplex n hn e s)))

end Work.BridgeSquare
