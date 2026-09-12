import Mathlib.RingTheory.Localization.AtPrime.Basic

namespace Commons.RingTheory.Ideal

theorem mem_minimalPrimes_of_localization_iso_field {A K : Type} [CommRing A] [Field K]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hiso : Nonempty (Localization.AtPrime 𝔭 ≃+* K)) :
    𝔭 ∈ Ideal.minimalPrimes (⊥ : Ideal A) := by
  have hField : IsField (Localization.AtPrime 𝔭) :=
    (hiso.some.toMulEquiv).isField (Field.toIsField K)
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp hField
  have hmap : Ideal.map (algebraMap A (Localization.AtPrime 𝔭)) 𝔭 = ⊥ := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, hmax]
  rw [Ideal.minimalPrimes, Set.mem_ofPred_eq]
  unfold Ideal.IsMinimalPrime Minimal
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro q ⟨hq, -⟩ hle x hx
  have hx0 : algebraMap A (Localization.AtPrime 𝔭) x = 0 := by
    have hmem : algebraMap A (Localization.AtPrime 𝔭) x ∈
        Ideal.map (algebraMap A (Localization.AtPrime 𝔭)) 𝔭 :=
      Ideal.mem_map_of_mem _ hx
    rw [hmap] at hmem
    simpa using hmem
  rw [IsLocalization.map_eq_zero_iff (M := 𝔭.primeCompl)] at hx0
  obtain ⟨m, hm⟩ := hx0
  have hmemq : (m : A) * x ∈ q := by rw [hm]; exact q.zero_mem
  rcases hq.mem_or_mem hmemq with h | h
  · exact absurd (hle h) m.2
  · exact h

end Commons.RingTheory.Ideal