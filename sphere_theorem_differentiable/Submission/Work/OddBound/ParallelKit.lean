import Submission.ParallelGlobal
import Submission.ParallelRoom
import Submission.SyngePackage
import Submission.ParallelBridge
import Submission.ParallelField
import Submission.SyngeFieldR
import Submission.ChartConnection
import Submission.SyngeInput

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Re-export of the parallel-transport toolkit (for `Submission/Work/OddBound/*` lemmas)

This module imports nothing of its own: it exists so that the lemmas about
`Work.OddBound.ParallelNormalPair` (`Submission/Work/OddBound/IndexBound.lean`) can be proved
against the global parallel-field machinery of `Submission/ParallelGlobal.lean`,
`Submission/ParallelRoom.lean` (`parallelFieldR`, `parallelFieldR_spec`, `covAlong_parallelFieldR`)
and `Submission/SyngePackage.lean` (`velocity_eq_parallelField`, `inner_parallelField_eq`), which are
declared in the main tree and cannot be named in a `depends_on` list.
-/
