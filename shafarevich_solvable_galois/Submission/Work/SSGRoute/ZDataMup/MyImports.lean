/-
Shared import umbrella for the conductor-drop work (`ZDataMup` lane).
-/
import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinSetup
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage
import Submission.NK.CFTLib.hilbertReciprocity_cyclic
import Submission.NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.CFTLib.IdeleHasse.localFaithful_onePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
