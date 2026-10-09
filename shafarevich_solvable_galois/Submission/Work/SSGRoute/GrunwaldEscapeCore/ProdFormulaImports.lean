import Mathlib
import Submission.Work.SSGRoute.ZDataMup.localFactorProductFormulaAux
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import hub for the commutative product formula

Collects, in one module under `Submission/Work`, the vocabulary needed to *state*
`prod_localFactor_eq_one_of_comm` (the commutative-target form of
`Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one`).
-/
