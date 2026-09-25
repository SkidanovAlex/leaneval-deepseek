import Mathlib
import Submission.NK.CFTLib.HR.TransferAux.Defs
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NK.GlobalCFT CategoryTheory
open scoped NumberField

namespace NK.CFTLib.HR.TransferAux

open IsDedekindDomain IdeleHasse

attribute [local instance 5000] Rep.hV1 Rep.hV2


end NK.CFTLib.HR.TransferAux
