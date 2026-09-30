/-
# The facet data of the cells of `M̄`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`: the finite check that the cell of a
facet node of the root face of a cell of dimension `n` has dimension `n - 1`.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.AtlasData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option autoImplicit false

namespace Work.MbarHomology.Mbar

open Work.Subdivision Work.ConvexCells
open scoped BigOperators

noncomputable section

/-- The dimension of the cell of a node is the dimension of its face. -/
theorem moDim_moCell (c : ZMod 2) (F : Fin 865) : moDim (moCell c F) = QbarCW.dim ⟨F⟩ := by
  decide +revert

/-- **The facet data**: the cell of a facet node of the root face of a cell of dimension `n` has
dimension `n - 1`.  Stated in the `filter = ∅` form so that the decidability instance is small. -/
theorem moDim_facet_filter (n : Fin 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    (qFacet (moRoot (moCid n e))).filter
      (fun G => moDim (moCell (moRootC (moCid n e)) G) + 1 ≠ (n : ℕ)) = ∅ := by
  decide +revert

/-- The dimension of the cell of a facet node of a cell of dimension `n`. -/
theorem moDim_facet (n : Fin 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n))
    (G : Fin 865) (hG : G ∈ qFacet (moRoot (moCid n e))) :
    moDim (moCell (moRootC (moCid n e)) G) + 1 = (n : ℕ) := by
  by_contra h
  have hmem : G ∈ (qFacet (moRoot (moCid n e))).filter
      (fun G => moDim (moCell (moRootC (moCid n e)) G) + 1 ≠ (n : ℕ)) :=
    Finset.mem_filter.mpr ⟨hG, h⟩
  rw [moDim_facet_filter n e] at hmem
  exact absurd hmem (by simp)

end

end Work.MbarHomology.Mbar
