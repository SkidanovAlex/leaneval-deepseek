import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.inertia_eq_bot_of_finset_sup
import Submission.Work.SSGRoute.Sha2Lib.inertia_eq_bot_of_sup
import Submission.Work.SSGRoute.Sha2Lib.normalClosureEqTop
import Submission.Work.SSGRoute.Sha2Lib.normalClosure_le_sup_conjugates
import Submission.Work.SSGcrux.inertia_eq_bot_of_finset_sup_mid
import Submission.Work.SSGRoute.TPatom.ramificationIdx_eq_one_normalClosure
import Submission.Work.SSGRoute.Sha2Lib.exists_cyclic_p_level_split_inert
import Submission.Work.SSGRoute.Sha2Lib.restrictNormalHom_eq_one_of_isInertiaAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TPatom

theorem levelInertiaEqBot {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (K1 : IntermediateField k K) [NumberField ↥K1] [FiniteDimensional k ↥K1] [IsGalois k ↥K1]
    (l : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (E : IntermediateField ↥K1 Ω) [NumberField ↥E] [FiniteDimensional ↥K1 ↥E] [IsGalois ↥K1 ↥E]
    (hEunr : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
      (𝔮.asIdeal.under (NumberField.RingOfIntegers ↥K1)).LiesOver l.asIdeal →
      𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K1) = 1)
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hL : (L : Set Ω) = (IntermediateField.normalClosure k
      ↥((IsScalarTower.toAlgHom k K Ω).fieldRange ⊔ E.restrictScalars k) Ω : Set Ω))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hql : q.asIdeal.LiesOver l.asIdeal)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal) :
    Ideal.inertia (↥L ≃ₐ[K] ↥L) q'.asIdeal = ⊥ := by sorry

end Work.SSGRoute.TPatom
