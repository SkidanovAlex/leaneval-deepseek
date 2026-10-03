import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.Defs
import Submission.Lib.Unif2.ChartLogClamp
import Submission.Lib.Unif2.GreenConditional
import Submission.Lib.Unif2.SuperharmonicX
import Submission.Lib.Unif2.MaxPrincipleRegion
import Submission.Lib.Unif2.DirichletLim
import Submission.Lib.Unif2.BarrierComparison
import Submission.Lib.Unif2.DirichletX
import Submission.Lib.Unif2.ChartBallDirichlet

/-!
# Shared imports for the barrier-regular Green function lemmas

A convenience module collecting the imports that the statements of
`Work/SimplyConnected/ABS/exists_isGreenOn_of_barriers.lean` and of the lemmas it depends on
(the superharmonic majorant of the clamped logarithmic potential, and the connectivity/positivity
inputs of the sweep construction) refer to, so that the delegated lemmas can list
`SimplyConnected/ABS/GreenSetupReg` in their `depends_on`.

Nothing of mathematical substance lives here.
-/
