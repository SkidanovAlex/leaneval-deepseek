import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one
import Submission.NK.CFTLib.Arl.artinSym_normIdeleHom_ideleOfPrime_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The Artin-symbol chapter: everything proved so far

Consistency module: it re-exports the definitions and the proved lemmas of the chapter so that
downstream work (`exists_monoidHom_ideleArtin`, the norm-killing chapter, `hle`) can import one
module. -/
