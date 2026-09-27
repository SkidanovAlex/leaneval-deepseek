import Submission.Work.Final.Main
import Submission.Work.Final.SkeletonFix
import Submission.Work.Final.not_forall_isClosed_Low
import Submission.Work.Final.skeletonDataFin

/-!
# `Submission.Work.Final`: import this for the final assembly

The entry point is `Work.Final.poincare_high_dim_topological_of_inputs`
(`Submission/Work/Final/Main.lean`): the challenge theorem modulo the single holder
`Work.Final.FinalInputs n` (Newman's engulfing theorem `E0`, owned by `Submission/Work/Engulf`).

See `Submission/Work/Final/NOTES_Final.md` for the chain, the list of holders and their owners, and
the `SkeletonData` interface repair (`Work.Final.skeletonData`,
`Work.Final.SkeletonDataFin`).  `Submission/Work/Final/Usage.lean` has worked examples and
`Submission/Work/Final/Audit.lean` prints the axiom audits.
-/
