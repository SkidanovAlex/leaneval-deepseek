import Mathlib
import Submission.Work.SSGRoute.ZDataMup.MyImports
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langX2KernelLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_one_of_kernelLe_of_relIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langCyclicRelIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.exists_admissible
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_cyclic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_independent_of_congruence_data
import Submission.Work.SSGRoute.ZDataMup.artinKillsPrincipal_of_isAdmissible
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Import umbrella for the "Frobenius normalisation at every unramified prime" lane
(`Work.SSGRoute.ZDataMup.ideleArtin_frobAtPrime_unramifiedLane`): re-exports the Lang/Artin
reciprocity machinery, the idèlic Artin map and its restriction/interdependence lemmas, so that
lemmas delegated inside `Submission/Work` can state them. -/
