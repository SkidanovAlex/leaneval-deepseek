import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.centralizer_fitting_eq_center
import Submission.Work.Fitting.centralizer_fitting_le
import Submission.Work.Fitting.centralizer_pPrimePCore_le
import Submission.Work.Fitting.exists_chiefSeries
import Submission.Work.Fitting.exists_isMinimalNormal_le
import Submission.Work.Fitting.fitting_eq_bot_iff
import Submission.Work.Fitting.fitting_eq_iInf_chiefSeries
import Submission.Work.Fitting.fitting_eq_iSup_pCore
import Submission.Work.Fitting.fitting_eq_pCore_of_pPrimeCore_eq_bot
import Submission.Work.Fitting.fitting_eq_sInf_chiefFactor_centralizer
import Submission.Work.Fitting.fitting_eq_top_iff
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.fitting_le_fitting_of_normal
import Submission.Work.Fitting.fitting_le_sectionCentralizer
import Submission.Work.Fitting.fitting_ne_bot
import Submission.Work.Fitting.fitting_prod
import Submission.Work.Fitting.fitting_quotient_frattini
import Submission.Work.Fitting.frattini_le_fitting
import Submission.Work.Fitting.isChiefFactor_iff_isMinimalNormal_map
import Submission.Work.Fitting.isChiefFactor_isMinimalNormal_map
import Submission.Work.Fitting.isMinimalNormal_commutator_eq_self
import Submission.Work.Fitting.isMinimalNormal_isPGroup
import Submission.Work.Fitting.isMinimalNormal_isPGroup_commutative
import Submission.Work.Fitting.isMinimalNormal_isPGroup_or_pPrime
import Submission.Work.Fitting.isNilpotent_iff_iSup_pCore_eq_top
import Submission.Work.Fitting.isNilpotent_of_commutator_le_center
import Submission.Work.Fitting.isPSolvable_of_solvable
import Submission.Work.Fitting.isPSolvable_quotient
import Submission.Work.Fitting.isPSolvable_subgroup
import Submission.Work.Fitting.le_pPrimePCore_of_map_isPiNat
import Submission.Work.Fitting.le_sectionCentralizer_iff
import Submission.Work.Fitting.map_fitting_le
import Submission.Work.Fitting.mem_piCore_iff
import Submission.Work.Fitting.mem_sectionCentralizer_iff_commutator
import Submission.Work.Fitting.nilpotent_sup_of_normal
import Submission.Work.Fitting.pCoreSeries_characteristic
import Submission.Work.Fitting.pCoreSeries_mono
import Submission.Work.Fitting.pCoreSeries_one
import Submission.Work.Fitting.pCoreSeries_three
import Submission.Work.Fitting.pCoreSeries_two
import Submission.Work.Fitting.pCore_eq_iInf_sylow
import Submission.Work.Fitting.pCore_eq_top_iff
import Submission.Work.Fitting.pCore_le_fitting
import Submission.Work.Fitting.pCore_le_pPrimePCore
import Submission.Work.Fitting.pCore_le_sylow
import Submission.Work.Fitting.pLength_eq_zero_iff
import Submission.Work.Fitting.pLength_le_iff
import Submission.Work.Fitting.pLength_le_one_iff_normal_sylow
import Submission.Work.Fitting.pLength_le_pLength_of_subgroup
import Submission.Work.Fitting.pLength_quotient_le
import Submission.Work.Fitting.pLength_quotient_pPrimeCore
import Submission.Work.Fitting.pLength_spec
import Submission.Work.Fitting.pPrimeCore_eq_top_of_not_prime
import Submission.Work.Fitting.pPrimePCore_characteristic
import Submission.Work.Fitting.pPrimePCore_map_eq
import Submission.Work.Fitting.piCoreSet_sup
import Submission.Work.Fitting.piCore_eq_top_iff
import Submission.Work.Fitting.piCore_inf_eq_bot_of_coprime
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.piCore_quotient_eq_bot
import Submission.Work.Fitting.piCore_sup_le_piCore_union
import Submission.Work.Fitting.sectionCentralizer_antitone_right
import Submission.Work.Fitting.sectionCentralizer_bot
import Submission.Work.Fitting.sectionCentralizer_mono_left
import Submission.Work.Fitting.subsingleton_of_pCore_eq_bot_of_pPrimeCore_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.Main`: the Fitting subgroup, π-cores and p-length (area A2)

Aggregator module for area A2 (Fitting subgroup, π-cores, p-length, chief factors).
See `Submission/Work/Fitting/NOTES.md` for the full description of the area.
-/
