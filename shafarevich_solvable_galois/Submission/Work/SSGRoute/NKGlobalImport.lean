import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localUnits_iff_localAlgebraMapUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Umbrella re-export of the NK global-CFT vocabulary (idèles, places, local units, the
inclusion of idèle groups) for lemmas stated in `Submission/Work/SSGRoute`. -/
