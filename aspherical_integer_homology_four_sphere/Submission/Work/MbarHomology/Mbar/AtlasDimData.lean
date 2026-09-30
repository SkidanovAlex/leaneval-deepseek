/-
# The dimension data of the nodes of `M̄`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`: the finite checks relating the dimension
`moDim (moCell c F)` of the cell of a node to the dimension of the face `F` in the poset
`QbarCW`.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.AtlasNodeData

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

theorem moPos_lt (i : Fin 482) :
    moPos i < Work.HomologyIso.Gen.mbarDim (moDim i) := by decide +revert

/-- The dimension of the cell of a node is the dimension of its face in `QbarCW`. -/
theorem moDim_moCell (c : ZMod 2) (F : Fin 865) :
    moDim (moCell c F) = QbarCW.dim ⟨F⟩ := by decide +revert

end

end Work.MbarHomology.Mbar
