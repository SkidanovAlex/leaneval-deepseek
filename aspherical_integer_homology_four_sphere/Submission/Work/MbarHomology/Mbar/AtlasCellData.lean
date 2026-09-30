/-
# The dimension data of the cells of `M̄`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`: the finite checks relating the cell
tables `moDim`, `moPos`, `moRoot` of `Submission/Work/MbarHomology/Data/MbarOrbits.lean` to the
face poset `QbarCW` and its cell dimension.
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

/-! ## The dimension data -/

theorem moCid_spec (n : Fin 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    moDim (moCid n e) = (n : ℕ) ∧ moPos (moCid n e) = (e : ℕ) := by decide +revert

theorem moRoot_dim (n : Fin 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    QbarCW.dim ⟨moRoot (moCid n e)⟩ = (n : ℕ) := by decide +revert


end

end Work.MbarHomology.Mbar
