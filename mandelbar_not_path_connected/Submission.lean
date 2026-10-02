import ChallengeDeps
import Submission.Helpers
import Submission.Work.MandelWire.NoPortrait
import Submission.Work.PARIMPL2.Lavaurs.MandelWireExport
import Submission.Work.SatFree.exists_saturated

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open LeanEval.ComplexAnalysis
open Function

namespace Submission

/-- The mandelbar is not path-connected: the wiring
`Work.MandelWire.mandelbar_not_path_connected_of_lav_sat` with PARIMPL2's Lavaurs phase and
SatFree's saturated flower. -/
theorem mandelbar_not_path_connected : ¬ IsPathConnected Mandelbar :=
  Work.MandelWire.mandelbar_not_path_connected_of_lav_sat
    Work.PARIMPL2.Lavaurs.lavaursPhase Work.SatFree.exists_saturated

end Submission
