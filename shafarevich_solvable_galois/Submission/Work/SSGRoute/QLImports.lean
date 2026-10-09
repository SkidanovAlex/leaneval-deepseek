/-
Re-export module for `Work.SSGRoute.exists_level_quotientNorm_avoids` and its helper lemmas:
aggregates the NK/Commons results that the helpers need, so that delegated lemmas can list a
single `depends_on` entry.
-/
import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_realization
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_cyclic
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localFixed_all
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.CFTLib.IdeleHasse.Crux.localNormRep
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.LocalUnitsSub
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.HassePrinciple.exists_fixed_uniformizer_localAutHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
