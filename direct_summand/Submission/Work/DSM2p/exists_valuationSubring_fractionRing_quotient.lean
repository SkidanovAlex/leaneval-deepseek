import Mathlib

namespace Work.DSM2p

/-- The quotient `V ⧸ P` of a valuation subring `V` by a prime ideal `P` is again a
valuation ring; consequently its image in its fraction field is the carrier of a
valuation subring of that fraction field. -/
theorem exists_valuationSubring_fractionRing_quotient {K : Type*} [Field K]
    (V : ValuationSubring K) (P : Ideal V) [P.IsPrime] :
    ∃ W : ValuationSubring (FractionRing (V ⧸ P)),
      W.toSubring = (algebraMap (V ⧸ P) (FractionRing (V ⧸ P))).range := by
  -- A quotient of a valuation ring by a prime ideal is again a valuation ring.
  haveI : ValuationRing (V ⧸ P) :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  -- For a valuation ring `𝒪` with fraction field `K`, every `x : K` satisfies
  -- `x = algebraMap 𝒪 K a` or `x⁻¹ = algebraMap 𝒪 K a` for some `a : 𝒪`.
  obtain ⟨h, _⟩ := (ValuationRing.isFractionRing_iff (𝒪 := V ⧸ P)
      (K := FractionRing (V ⧸ P))).mp inferInstance
  refine ⟨ValuationSubring.ofSubring _ ?_, ValuationSubring.ofSubring_toSubring _ _⟩
  intro x
  rcases h x with ⟨a, ha | ha⟩
  · left; rw [RingHom.mem_range]; exact ⟨a, ha.symm⟩
  · right; rw [RingHom.mem_range]; exact ⟨a, ha.symm⟩

end Work.DSM2p
