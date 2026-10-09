import Submission.Work.SSGRoute.NKGlobalImport
import Submission.NK.GlobalCFT.Reciprocity
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.CFTLib.IdeleHasse.localFaithful_onePlace
import Submission.NK.CFTLib.IdeleHasse.badSet_not_singleton
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.CFTLib.hilbertReciprocity_cyclic
import Submission.NK.GlobalCFTdeep.Inequalities
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.CFTLib.IdeleHasse.exists_localMap_ofFinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Umbrella re-export of the Artin-reciprocity vocabulary used by the `μ_p` local Tate system

This module is only an import umbrella: it re-exports the workspace's global and local class field
theory (the local–global Artin map, the local factors, Hilbert reciprocity in the "one place
omitted" form, the norm-index theorem and the idèlic Artin map) so that lemmas delegated inside
`Submission/Work` can state the product-form reciprocity without depending on `Submission.NK`
modules directly.
-/
