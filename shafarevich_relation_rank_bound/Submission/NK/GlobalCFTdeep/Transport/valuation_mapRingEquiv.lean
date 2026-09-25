import Mathlib
import Submission.NK.GlobalCFTdeep.Transport.PlaceDefs
import Submission.NK.NumberTheory.NumberField.Completion.place_transport

namespace NK.GlobalCFTdeep.Transport

open IsDedekindDomain

/-- **Compatibility of the `v`-adic valuation on the ring of integers with a ring equivalence.**

For a ring equivalence `e : R ≃+* S` between Dedekind domains and a height one prime `v` of `R`,
the transported height one prime `heightOneSpectrumCongr e v` (whose underlying ideal is
`v.asIdeal.map e`) computes at `e r` the same value that `v` computes at `r`,

`(heightOneSpectrumCongr e v).intValuation (e r) = v.intValuation r`.

This is the general form of `Commons.NumberTheory.NumberField.intValuation_ringOfIntegersRingEquiv`,
which is the case of a `ℚ`-algebra isomorphism of number fields; here no compatibility with the
base ring is assumed, which is what the transport along an arbitrary ring equivalence of number
fields requires.  Both sides are written with `intValuation_eq_exp_neg_multiplicity`, and the
multiplicities agree because `Ideal.map` along `e` is a multiplicative equivalence of the ideal
monoids (`idealMapMulEquiv`), along which `multiplicity` is invariant (`multiplicity_map_eq`). -/
theorem intValuation_heightOneSpectrumCongr {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S) (v : HeightOneSpectrum R) (r : R) :
    (NK.UniverseUnify.heightOneSpectrumCongr e v).intValuation (e r) = v.intValuation r := by
  rcases eq_or_ne r 0 with h | h
  · subst h; simp
  · have hne : e r ≠ 0 := fun hz => h (e.injective (by simpa using hz))
    have hasIdeal : (NK.UniverseUnify.heightOneSpectrumCongr e v).asIdeal =
        Ideal.map (e : R →+* S) v.asIdeal :=
      NK.UniverseUnify.heightOneSpectrumMapRingEquiv_asIdeal e v
    have hspan : Ideal.span {e r} = (Ideal.span {r}).map (e : R →+* S) := by
      rw [Ideal.map_span]; simp
    have hmult : multiplicity (Ideal.map (e : R →+* S) v.asIdeal)
        (Ideal.map (e : R →+* S) (Ideal.span {r})) =
        multiplicity v.asIdeal (Ideal.span {r}) := by
      have hh := multiplicity_map_eq (Commons.NumberTheory.NumberField.idealMapMulEquiv e)
        (a := v.asIdeal) (b := Ideal.span {r})
      rw [Commons.NumberTheory.NumberField.idealMapMulEquiv_apply,
        Commons.NumberTheory.NumberField.idealMapMulEquiv_apply] at hh
      simpa using hh
    rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hne,
      HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ h, hasIdeal, hspan, hmult]

theorem valuation_mapRingEquiv {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : K ≃+* K') (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) : (NK.GlobalCFTdeep.Transport.finitePlaceEquiv e Q).valuation K' (e x) = Q.valuation K x := by
  obtain ⟨⟨r, s⟩, hrs⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (NumberField.RingOfIntegers K)) x
  have hs : NumberField.RingOfIntegers.mapRingEquiv e (↑s : NumberField.RingOfIntegers K) ≠ 0 := by
    rw [← map_zero (NumberField.RingOfIntegers.mapRingEquiv e)]
    exact fun hz => (nonZeroDivisors.coe_ne_zero s)
      ((NumberField.RingOfIntegers.mapRingEquiv e).injective hz)
  have hcoe : e (IsLocalization.mk' K r s) =
      IsLocalization.mk' K' (NumberField.RingOfIntegers.mapRingEquiv e r)
        ⟨NumberField.RingOfIntegers.mapRingEquiv e (↑s), mem_nonZeroDivisors_of_ne_zero hs⟩ := by
    rw [IsFractionRing.mk'_eq_div, map_div₀, IsFractionRing.mk'_eq_div]
    simp
  rw [← hrs, hcoe, IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    IsDedekindDomain.HeightOneSpectrum.valuation_of_mk']
  show (NK.UniverseUnify.heightOneSpectrumCongr (NumberField.RingOfIntegers.mapRingEquiv e) Q).intValuation
      (NumberField.RingOfIntegers.mapRingEquiv e r) /
      (NK.UniverseUnify.heightOneSpectrumCongr (NumberField.RingOfIntegers.mapRingEquiv e) Q).intValuation
      (NumberField.RingOfIntegers.mapRingEquiv e (↑s)) = Q.intValuation r / Q.intValuation ↑s
  rw [intValuation_heightOneSpectrumCongr (NumberField.RingOfIntegers.mapRingEquiv e) Q r,
    intValuation_heightOneSpectrumCongr (NumberField.RingOfIntegers.mapRingEquiv e) Q (↑s)]

end NK.GlobalCFTdeep.Transport
