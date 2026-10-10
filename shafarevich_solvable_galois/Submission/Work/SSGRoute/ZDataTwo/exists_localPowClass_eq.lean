import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.NormNum.Prime
import Submission.Work.HilbertSymbolGeneral.canonicalAPI
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
import Submission.Work.SSGRoute.ZDataTwo.Mu2InvolutionForm
import Submission.Work.SSGRoute.ZDataTwo.exists_level_localNormSubgroup_eq
import Submission.Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple
import Submission.Work.SSGRoute.exists_kummerChar_of_additive_locConst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

theorem exists_localPowClass_eq {k : Type} [Field k] [NumberField k]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (u : (Q.adicCompletion k)ˣ) :
    ∃ (b : kˣ) (c : (Q.adicCompletion k)ˣ),
      c ∈ NK.UchidaKummer.ellPowSubgroup (Q.adicCompletion k) 2 ∧
      Units.map (algebraMap k (Q.adicCompletion k)).toMonoidHom b = u * c := by
  classical
  let S : Finset (NK.Chebotarev.PrimeIdeal k) := {Q}
  have hQ : Q ∈ S := Finset.mem_singleton_self Q
  have hsurj := NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
    (K := k) 2 S (NK.UchidaKummer.Approximation.isWeakApproximation k S)
    (NK.UchidaKummer.Approximation.isOpenEllPowSubgroup k 2 (by norm_num))
  obtain ⟨b, hb⟩ := hsurj (fun 𝔮 => by
    have hq : 𝔮.1 = Q := Finset.mem_singleton.mp 𝔮.2
    rw [hq]
    exact QuotientGroup.mk' _ u)
  refine ⟨b, ((Units.map (algebraMap k (Q.adicCompletion k)).toMonoidHom b)⁻¹ * u)⁻¹, ?_, ?_⟩
  · have h := hb ⟨Q, hQ⟩
    have h2 : QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (Q.adicCompletion k) 2)
        (Units.map (algebraMap k (Q.adicCompletion k)).toMonoidHom b)
        = QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (Q.adicCompletion k) 2) u := by
      simpa [NK.UchidaKummer.localPowClass] using h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
    exact Subgroup.inv_mem _ h2
  · rw [mul_inv_rev, inv_inv]
    group

end Work.SSGRoute.ZDataTwo
