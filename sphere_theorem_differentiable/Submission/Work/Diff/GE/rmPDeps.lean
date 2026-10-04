import Mathlib
import Submission.ChartBounds
import Submission.ChartConnection
import Submission.ChartCurv
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.GE.cGram_eq_sum_gramInv
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing
import Submission.Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth
import Submission.Work.Diff.EXT.kosDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Re-export module for the `rmP_jointSmooth` development

The pieces of the proof that the pointwise curvature form `rmP` of a jointly smooth family of
metrics is jointly smooth are delegated to colleagues whose statement files may only import
modules listed in `depends_on`; `depends_on` paths must have at least a topic directory and a name,
so top-level modules of the seeded library (`Submission.ChartConnection`, `Submission.ChartCurv`,
`Submission.ChartBounds`) cannot be listed directly.  This module re-exports everything the
delegated statements need.  Nothing here is mathematics.
-/
