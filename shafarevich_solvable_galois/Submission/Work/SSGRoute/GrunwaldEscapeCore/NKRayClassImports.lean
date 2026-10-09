import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.exists_ideal_of_class
import Submission.NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff
import Submission.NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup
import Submission.NK.CFTLib.Existence.splitting_of_normClass
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Existence.classField_exists_primeIndex
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.ssg8Chebotarev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Imports for the ray-class Čebotarev input of the Grünwald escape correction

This module only collects the (already proved) global class field theory modules that the
arithmetic core of `Work.SSGRoute.GrunwaldEscapeCore.grunwald_escape_correction` uses:

* `NK.NUV2.RouteB.Modulus`, `…CongSubgroup`, the ray class group `I(𝔪)/P(𝔪)` and the fact that
  *every* ray class contains an integral ideal coprime to `𝔪`
  (`NK.NUV2.RouteB.RayModulus.exists_ideal_of_class`);
* the finiteness of the ray class group (`NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup`);
* the existence theorem for the class field of an open subgroup of arbitrary index
  (`Work.SSGRoute.CFTSide.classField_exists_of_index`);
* the idèlic Artin map: the Frobenius normalisation `art (ideleOfPrime 𝔭) = frobAtPrime 𝔭` for
  `𝔭 ∤ m` and the splitting law (`NK.CFTLib.Existence.splitting_of_normClass`,
  `NK.CFTLib.Arl.exists_monoidHom_ideleArtin`);
* Čebotarev's density theorem over an arbitrary number field base in existence form
  (`Work.SSGRoute.exists_isFrobAtPrime_notMem_density`, `Work.SSGRoute.chebotarev_density_general`).
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

end Work.SSGRoute.GrunwaldEscapeCore
