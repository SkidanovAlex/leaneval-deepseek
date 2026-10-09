import Mathlib
import Submission.NK.CFTLib.IdeleHasse.exists_localMap_ofFinite
import Submission.NK.CFTLib.IdeleHasse.localFaithful_onePlace
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.ideleGluing
import Submission.NK.NUV2.ARL.isOpenNorm
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.NK.NUV2.ARL.unifUnit_pow_mem_localNormSubgroup
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Import hub for the arithmetic core
`Work.SSGRoute.ZDataMup.mup_localArtin_productFormula` (the `mu_p` product formula for the honest
local Artin family).  See `Submission/Work/SSGRoute/ZDataMup/NOTES_mup_localArtin_productFormula.md`
and the docstrings of `SSGRoute/ZDataMup/localTateSystem_productFormula.lean` for the reduction of
the node `Work.SSGRoute.ZDataMup.localTateSystem_productFormula_odd` to that statement and for the
route through the local-global compatibility of the Artin map. -/
