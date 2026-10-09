import Mathlib
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.PT.e1a_can_chain
import Submission.Work.SSGRoute.PT.e1a_localComparison_bricks
import Submission.Work.SSGRoute.PT.akH2Setup
import Submission.Work.SSGRoute.PT.exists_localField_place_data
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
import Submission.Work.SSGRoute.PT.homCoindFreeT_H1_subgroup
import Submission.Work.SSGRoute.PT.e1a_seam
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.E1cGeneric.ext_localUnits_iso_Q_general
import Submission.Work.SSGRoute.E1cGeneric.ext_res_mulEquiv_n_rules
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.ExtChain.e1aDelta_natural
import Submission.Work.SSGRoute.PT.H1Transfer
import Submission.Work.SSGRoute.localGaloisEquiv_coInAdjoin_compat_general
import Submission.Work.SSGRoute.E1aClean.Transport
import Submission.Work.SSGRoute.E1aClean.LocalData
import Submission.Work.SSGRoute.E1aClean.exists_localData_with_seam
import Submission.Work.SSGRoute.HomCoindSubgroup.homCoindFreeT_H1_subgroup_inf
import Submission.Work.SSGRoute.PT.h1TransferAddHom_delta
import Submission.Work.SSGRoute.PT.e1a_deltaH1_natural
import Submission.Work.SSGRoute.E1aClean.PhiERules
import Submission.Work.SSGRoute.E1aClean.finLocalCriterion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

theorem extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [hfin : Module.Finite ℤ ↑(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)).V]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (z : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
        (SSGRoute.PTExt.unitsK k K) 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Work.SSGRoute.ExtChain.e1cEquiv
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0 →
      (SSGRoute.PTExt.extRes
          (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite q)).subtype z).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.unitsToLocalUnits k K (NK.GlobalCFT.Place.ofFinite q)))
        (add_zero 1) = 0 :=
  Work.SSGRoute.E1aClean.finLocalCriterion k Ω K N A hA q hAq z

end Work.SSGRoute.PT
