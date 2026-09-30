import Mathlib
import Submission.Work.BridgeSquare.fibreSteps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Work.BridgeSquare

theorem edgeFace_struct_j1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    Work.Subdivision.PolyCW.dim Work.MbarHomology.QbarCW
        (⟨Work.BridgeSquare.edgeFace v 1 k⟩ : Work.MbarHomology.QbarCell) = 1
    ∧ Work.Subdivision.PolyCW.facets Work.MbarHomology.QbarCW
        (⟨Work.BridgeSquare.edgeFace v 1 k⟩ : Work.MbarHomology.QbarCell)
        = {(⟨Work.BridgeSquare.edgeW0Face v 1 k⟩ : Work.MbarHomology.QbarCell),
           (⟨Work.BridgeSquare.edgeW1Face v 1 k⟩ : Work.MbarHomology.QbarCell)}
    ∧ Work.MbarHomology.qInc (Work.BridgeSquare.edgeFace v 1 k) (Work.BridgeSquare.edgeW0Face v 1 k)
        = - Work.MbarHomology.qInc (Work.BridgeSquare.edgeFace v 1 k) (Work.BridgeSquare.edgeW1Face v 1 k)
    ∧ Work.BridgeSquare.edgeSign v 1 k * Work.MbarHomology.qInc (Work.BridgeSquare.edgeFace v 1 k)
          (Work.BridgeSquare.edgeW0Face v 1 k) = (if (v : ℕ) = 4 then -1 else 1) := by
  revert hk
  fin_cases v <;> fin_cases k <;> decide

end Work.BridgeSquare
