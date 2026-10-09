import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.LocalCongruence
import Submission.Work.SSGRoute.ZDataTwo.AdicBridge
import Submission.Work.SSGRoute.ZConstruction.LocalSquares
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataTwo.FiniteReciprocity
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.Work.SSGRoute.ges_readoff
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.PlaceValBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo.TwoRec

theorem killsLocalGroup_of_one_unit {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (y : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hunit : A.valuation (algebraMap ↥K Ω (y : ↥K)) = 1)
    (ht : A.valuation (algebraMap ↥K Ω ((y : ↥K) - 1)) < 1) :
    ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ y u = 0 := by
  classical
  -- The place `A` of `Ω` restricts to a *finite* prime of `↥K`: a non-trivial place of `↥K`
  -- restricts to a non-trivial place of `k` because `↥K/k` is finite.
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro h
    apply hA
    have h1 : A.comap (algebraMap k Ω) =
        (A.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) := by
      have hcomp : (algebraMap k Ω) = (algebraMap ↥K Ω).comp (algebraMap k ↥K) := by
        ext x; exact IsScalarTower.algebraMap_apply k ↥K Ω x
      rw [hcomp]
      exact (ValuationSubring.comap_comap A (algebraMap ↥K Ω) (algebraMap k ↥K)).symm
    rw [h1, h]
    ext x
    simp
  -- The prime `𝔭` of `↥K` below `A`.
  obtain ⟨𝔭, h𝔭⟩ : ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
    ⟨Submission.NeukirchUchida.primeOf A hAK, Submission.NeukirchUchida.primeOf_spec A hAK⟩
  -- `y ≡ 1` modulo `𝔭`, transported to the completion.
  have hz : Valued.v (algebraMap ↥K (𝔭.adicCompletion ↥K) ((y : ↥K) - 1)) < 1 :=
    (adicCompletion_valuation_lt_one_iff A 𝔭 h𝔭 ((y : ↥K) - 1)).mpr ht
  -- `2` is a unit at `𝔭` (the place does not divide `2`).
  have h2u : IsUnit (2 : 𝔭.adicCompletionIntegers ↥K) :=
    isUnit_two_adicCompletionIntegers_of_not_lt_one 𝔭 fun hlt => h2 (by
      rw [← show algebraMap ↥K Ω (2 : ↥K) = (2 : Ω) from map_ofNat _ 2]
      exact (place_valuation_lt_one_iff A 𝔭 h𝔭 (2 : ↥K)).mpr hlt)
  -- Hensel at the completion: `y` is a square there.
  obtain ⟨c, hc⟩ := exists_sq_unitsMap_of_valued_sub_one_lt_one 𝔭 h2u y hz
  -- hence its local `2`-power class at `𝔭` is trivial.
  have hlocal : NK.UchidaKummer.localPowClass ↥K 2 𝔭 y = 1 :=
    Work.SSGRoute.localPowClass_eq_one_of_unit_component (p := 2) Nat.prime_two
      (γ := y) (e := (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom y)⁻¹)
      ⟨c⁻¹, by
        rw [powMonoidHom_apply]
        simpa [pow_two, mul_inv_rev] using congrArg Inv.inv hc⟩ rfl
  -- and the local Kummer dictionary converts that into the vanishing on the local group.
  intro u hu
  exact (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_eq_zero_iff_localPowClass K ζ hζK hζ y A hA
    𝔭 h𝔭).mpr hlocal u hu

end Work.SSGRoute.ZDataTwo.TwoRec
