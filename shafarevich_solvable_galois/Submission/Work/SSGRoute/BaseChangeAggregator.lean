import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_res_mulEquiv
import Submission.Work.SSGRoute.extH_congr
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Aggregator for `Work.SSGRoute.levelPair_baseChange_in`

Carries no declarations; provides the vocabulary of `E7bDefs` (hence `PTDefs`) together with the
transports used in the proof (`ext_res_mulEquiv`, `extH_congr`), the level-data existence lemmas
(`decompK_restrict_exists`, `localUnitsMap_exists`) and `localAlgebraMapUnits_self`.
-/
