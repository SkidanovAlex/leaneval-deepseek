import Mathlib
import Submission.Work.MbarHomology.Mbar.AtlasPush
import Submission.Work.MbarHomology.CellAtlas.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MbarHomology.Push

open Work.Subdivision
open scoped BigOperators

noncomputable section

/-- `pushNode c` intertwines the order-complex differential `D` on the subdivision of `Q̄` with
the transported `Δ`-complex differential `kδCpt mbarSd` on the chains of `mbarSd`. -/
theorem pushNode_comm_D (c : ZMod 2) (k : ℕ) (z : Work.Subdivision.chainMod Work.MbarHomology.QbarCW.Cell (k + 1)) :
    Work.MbarHomology.Mbar.pushNode c k (Work.Subdivision.D (α := Work.MbarHomology.QbarCW.Cell) k z)
      = Work.MbarHomology.CellAtlas.kδCpt Work.MbarHomology.mbarSd k (Work.MbarHomology.Mbar.pushNode c (k + 1) z) := by
  -- It suffices to check the identity on the standard generators.
  have hsingle : ∀ s : Simplex QbarCW.Cell (k + 1),
      Mbar.pushNode c k (D (α := QbarCW.Cell) k (Finsupp.single s 1))
        = CellAtlas.kδCpt mbarSd k (Mbar.pushNode c (k + 1) (Finsupp.single s 1)) := by
    intro s
    rw [D_single]
    rw [map_sum]
    simp only [map_smul, Mbar.pushNode_single]
    rw [CellAtlas.kδCpt_single]
    simp only [Mbar.nodeSimplex_face]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single a b =>
      rw [← Finsupp.smul_single_one (a := a) (b := b)]
      simp only [map_smul, hsingle]

end

end Work.MbarHomology.Push
