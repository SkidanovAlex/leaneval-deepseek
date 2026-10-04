/-
# The manifold layer: C1 bridge inputs

Collects the imports needed by the C1 bridge (`Man/Bridge.lean`): the chart packaging, its
properties, the agreement of the flat jets with the chart jets, the jet calculus, and the
jet-level DeTurck operator `pPhiJet` of `Submission/Work/Diff/STE/LieMet.lean`.
-/
import Mathlib
import Submission.Work.Diff.STE.Man.Defs
import Submission.Work.Diff.STE.Man.Basic
import Submission.Work.Diff.STE.Man.TorusInput
import Submission.Work.Diff.STE.Man.Jets
import Submission.Work.Diff.STE.Man.chartDatum_periodic_smooth
import Submission.Work.Diff.STE.Man.dpd_of_eventuallyEq_comp
import Submission.Work.Diff.STE.LieMet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
