import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff
import Submission.NK.NUV2.RouteB.RayModulus.exists_ideal_of_class
import Submission.NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.NK.CFTLib.Existence.splitting_of_normClass
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.CFTLib.Existence.classField_exists_primeIndex
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
import Submission.Work.SSGRoute.ssg8Chebotarev
import Submission.NK.NUV2.chebotarev_all0
import Submission.NK.Chebotarev.Basic
import Submission.NK.HeckeL.Consequences.exists_primeClass_eq
import Submission.NK.GlobalCFT.IdeleClassGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import bundle for the ray-class Čebotarev node

This module only collects the (already proved) global class field theory and Čebotarev
infrastructure used by

* `Work.SSGRoute.GrunwaldEscapeCore.gesChebotarev_rayClass`,
* `Work.SSGRoute.GrunwaldEscapeCore.isOpen_congSubgroup`,
* `Work.SSGRoute.GrunwaldEscapeCore.exists_abelian_classField_of_open_finiteIndex`,
* `Work.SSGRoute.GrunwaldEscapeCore.exists_artinMap_of_abelian`.

* the ray class group of a congruence subgroup and its finiteness
  (`NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup`);
* the openness of an idèle subgroup defined by local conditions
  (`Work.SSGRoute.isOpen_forall_mem_localUnits`, `RestrictedProduct.isOpen_forall_imp_mem`);
* the existence theorem of global class field theory at arbitrary index
  (`Work.SSGRoute.CFTSide.classField_exists_of_index`) and the abelian subextension with
  prescribed norm subgroup (`Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le`);
* the idèlic Artin map attached to a congruence subgroup and its Frobenius normalisation
  (`NK.CFTLib.Arl.exists_monoidHom_ideleArtin`, `NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin`,
  `NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup`);
* the ideal-theoretic Artin reciprocity law (`NK.CFTLib.artinReciprocityIdeal_proved`) and the
  fundamental class element (`NK.CFTLib.fundamentalClassElement`);
* the Hecke input (`NK.NUV2.heckeInput_proved`) and Čebotarev
  (`NK.NUV2.abelianLFunctions_of_freeInputs`,
  `NK.Chebotarev.infinite_setOf_isFrobAtPrime_of_abelianLFunctions`).
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

end Work.SSGRoute.GrunwaldEscapeCore
