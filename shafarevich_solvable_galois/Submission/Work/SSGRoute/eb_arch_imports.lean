import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Norm.NormTransAux
import Submission.NK.NUV2.ARL.HR.TransferSupport
import Submission.NK.NUV2.ARL.cyclotomic_isComplex
import Submission.NK.CFTLib.HR.isCyclotomic_onePlace_real
import Submission.NK.NUV2.ChebAux.Transfer.Defs
import Submission.NK.HR2.locUnits_inflation_eq_zero_iff
import Submission.NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero
import Submission.NK.HR2.exists_cycClassOf_of_res_eq_zero
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.HR2.transferStepOnePlace
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1
import Submission.Work.SSGRoute.eb_arch_crux
import Submission.Work.SSGRoute.E8Helpers
import Submission.Work.SSGRoute.eb_locUnits_resToGal
import Submission.Work.SSGRoute.phi1_level_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Umbrella re-export of the vocabulary needed by the archimedean case of
`brauer_single_place` (E8' piece P4) and its delegated lemmas: places of number fields, the local
unit localisation `NK.HassePrinciple.locUnits`, the level inflation `NK.NUV2.ARL.HR.inflation` and
the restriction `NK.NUV2.ChebAux.Transfer.resToGal`, the cyclotomic auxiliary vocabulary, and the
proved workspace helper lemmas (`Work.SSGRoute.eb_arch_crux`,
`Work.SSGRoute.eb_locUnits_resToGal`, `Work.SSGRoute.place_liesOver_trans`,
`Work.SSGRoute.not_liesOver_iff_not_mem_orbit`). -/
