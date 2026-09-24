import Mathlib
import Submission.Work.SimplyConnected.Defs
import Submission.ChartLogClamp
import Submission.GreenConditional
import Submission.SuperharmonicX
import Submission.MaxPrincipleRegion
import Submission.DirichletLim
import Submission.BarrierComparison
import Submission.DirichletX
import Submission.ChartBallDirichlet

/-!
# Shared imports for the barrier-regular Green function lemmas

A convenience module collecting the imports that the statements of
`Work/SimplyConnected/ABS/exists_isGreenOn_of_barriers.lean` and of the lemmas it depends on
(the superharmonic majorant of the clamped logarithmic potential, and the connectivity/positivity
inputs of the sweep construction) refer to, so that the delegated lemmas can list
`SimplyConnected/ABS/GreenSetupReg` in their `depends_on`.

Nothing of mathematical substance lives here.
-/
