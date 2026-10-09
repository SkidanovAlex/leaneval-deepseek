import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_finset_isBoundedIntegral
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.CFTLib.IdeleHasse.localFaithful_onePlace
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinSetup
import Submission.Work.Kummer.kummerPairing_bijective
import Submission.Work.Kummer.Defs
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup
import Submission.Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
import Submission.Work.SSGRoute.step4_y_escape_v2.localFactor_productFormula_clean
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
import Submission.Work.SSGRoute.ZDataMup.localFactor_towerCompat
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHomType
import Submission.Work.SSGRoute.step4_y_escape_v2.ReadOff
import Submission.Work.SSGRoute.n4_halpha_fix
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import hub for the orthogonality pieces of `GrunwaldEscapeCore`

Re-exports the global/local class field theory vocabulary (`localNormSubgroup`, `localImageAt`, the
one-place dictionary, the idèlic Artin map and the compatibility of its local factors in a tower,
the Kummer pairing) so that delegated statements about the orthogonality can name it through a
module path under `Submission/Work/`.
-/
