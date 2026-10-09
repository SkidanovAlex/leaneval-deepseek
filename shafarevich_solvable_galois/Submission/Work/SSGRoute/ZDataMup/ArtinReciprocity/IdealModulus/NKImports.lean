/-
Import umbrella for the ideal-modulus Artin reciprocity lane: the ideal-modulus vocabulary of
`IdealModulus/Defs.lean` together with the NK-layer Artin symbol and ramification machinery
(`NK.CFTLib.Arl.artinSym`, `NK.CFTLib.ArtinReciprocityIdeal.IsUnramified`, ...).
-/
import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
