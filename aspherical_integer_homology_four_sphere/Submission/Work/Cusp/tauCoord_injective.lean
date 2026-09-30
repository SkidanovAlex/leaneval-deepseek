import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

theorem tauCoord_injective (v : Fin 5) : Function.Injective (tauCoord v) := by
  intro x y h
  have h' : (tauCoord v x).1 = (tauCoord v y).1 := congrArg Prod.fst h
  simpa [tauCoord] using h'

end Work.Cusp
