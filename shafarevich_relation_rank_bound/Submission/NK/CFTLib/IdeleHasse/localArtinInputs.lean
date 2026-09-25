import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute
import Submission.Commons.NumberTheory.NumberField.Completion.exists_artinMap_of_abelian_local
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.IsFrobAtStabilizes
import Submission.NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg
import Submission.NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver
import Submission.NK.HeckeL.Basic
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists

/-!
# The local inputs for the local–global Artin map

A bridge module gathering, for the construction of the local factors of the local–global Artin map
`Φ = ∏_v λ_v`:

* the local Artin map of an unramified local extension with kernel the norm group
  (`Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_ramificationIdx_eq_one`);
* the general local Artin map of a finite abelian local extension
  (`Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute`);
* the identification of the local Galois group with the decomposition subgroup
  (`...decompositionSubgroupMulEquivLocalGalois`);
* the Frobenius API (`NK.Chebotarev`);
* the definition of the local norm subgroup `NK.CFTLib.IdeleHasse.localNormSubgroup`.
-/
