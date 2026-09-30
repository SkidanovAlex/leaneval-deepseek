/-
# Area LC (`Submission/Work/LeviCivita/`) — everything, in one import
-/
import Submission.Work.LeviCivita.Main
import Submission.Work.LeviCivita.LC
import Submission.Work.LeviCivita.ChartMetric
import Submission.Work.LeviCivita.FrameField
import Submission.Work.LeviCivita.Koszul
import Submission.Work.LeviCivita.Smooth
import Submission.Work.LeviCivita.isInvertible_of_posDef
import Submission.Work.LeviCivita.contDiffAt_chartGram
import Submission.Work.LeviCivita.contDiffAt_chartGramCLM
import Submission.Work.LeviCivita.contDiffAt_inverse_of_posDef
import Submission.Work.LeviCivita.contMDiffAt_mvfderiv_section
import Submission.Work.LeviCivita.contMDiffAt_chartGramCLM_inverse
import Submission.Work.LeviCivita.contMDiffAt_lcConn_pairing
import Submission.Work.LeviCivita.chartDg_eq_chartGram_chrB
import Submission.Work.LeviCivita.chartLCcoords_eventuallyEq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

