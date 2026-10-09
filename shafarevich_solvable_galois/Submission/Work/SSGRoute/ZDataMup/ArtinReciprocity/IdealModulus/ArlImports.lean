/-
Import umbrella for the `IdealModulus` lane of `ZDataMup`: the Arl-level principal-ray
congruence machinery (`artinSym_spanSingleton_eq_one_of_congr_pos` and its integral input), the
cyclotomic Artin reciprocity law (`artinReciprocity_cyclotomic`) and the Artin-symbol
homomorphism on the group of fractional ideals (`artinSymFracHom`).
-/
import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_integral
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_mem_congruence
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
