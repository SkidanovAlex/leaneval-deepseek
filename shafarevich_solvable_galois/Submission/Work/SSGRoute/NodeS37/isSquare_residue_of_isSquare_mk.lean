import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

theorem isSquare_residue_of_isSquare_mk {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (U : 𝔭.adicCompletionIntegers K) (r : NumberField.RingOfIntegers K)
    (hr : U - algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))
    (hsq : IsSquare (Ideal.Quotient.mk 𝔭.asIdeal r)) :
    IsSquare (IsLocalRing.residue (𝔭.adicCompletionIntegers K) U) := by
  classical
  -- The composite `𝓞 K → 𝔭.adicCompletionIntegers K → ResidueField` kills `𝔭`
  -- (indeed it kills exactly the elements of valuation `< 1`), so it factors through `𝓞 K ⧸ 𝔭`.
  have hker : ∀ a ∈ 𝔭.asIdeal,
      ((IsLocalRing.residue (𝔭.adicCompletionIntegers K)).comp
        (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K))) a = 0 := by
    intro x hx
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one]
    rw [Commons.NumberTheory.NumberField.adicCompletion_valued_algebraMap]
    exact (𝔭.intValuation_lt_one_iff_mem x).mpr hx
  let φ : (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) →+*
      IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K) :=
    Ideal.Quotient.lift 𝔭.asIdeal
      ((IsLocalRing.residue (𝔭.adicCompletionIntegers K)).comp
        (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K))) hker
  have hφ : ∀ x : NumberField.RingOfIntegers K,
      φ (Ideal.Quotient.mk 𝔭.asIdeal x) =
        IsLocalRing.residue (𝔭.adicCompletionIntegers K)
          (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) x) :=
    fun x => Ideal.Quotient.lift_mk _ _ _
  obtain ⟨s, hs⟩ := hsq
  refine ⟨φ s, ?_⟩
  -- the residue of `r : 𝓞 K` is the image of `r mod 𝔭`, whose square root `s` we transport
  have hs' : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
      (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) r) =
        φ s * φ s := by
    rw [← hφ r, hs, map_mul]
  -- `U` and `r` have the same residue because their difference lies in the maximal ideal
  have hU : IsLocalRing.residue (𝔭.adicCompletionIntegers K) U =
      IsLocalRing.residue (𝔭.adicCompletionIntegers K)
        (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) r) := by
    have h0 : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
        (U - algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) r) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hr
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  rw [hU, hs']

end Work.SSGRoute.NodeS37
