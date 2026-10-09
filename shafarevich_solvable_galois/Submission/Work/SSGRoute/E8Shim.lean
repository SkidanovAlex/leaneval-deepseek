import Mathlib
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero
import Submission.NK.HR2.locUnits_inflation_eq_zero_iff
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.NUV2.ChebAux.Transfer.Defs
import Submission.NK.NUV2.ARL.HR.TransferSupport
import Submission.Work.SSGRoute.eb_locUnits_resToGal
import Submission.Work.SSGRoute.phi1_level_naturality
import Submission.NK.CFTLib.HR.TransferAux.descent
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep
import Submission.NK.NUV2.Final.LevelInfIdentity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Shim: makes the `NK` vocabulary used by the E8' delegated lemmas available inside the
Mathlib-only delegation environment. -/
