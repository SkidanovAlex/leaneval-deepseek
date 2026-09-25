import Mathlib

namespace Work.CFTLib.PrimesAbove

theorem finset (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) :
    ∃ T' : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      (∀ w ∈ T', ∃ v ∈ T, w.asIdeal.LiesOver v.asIdeal) ∧
      (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (∃ v ∈ T, w.asIdeal.LiesOver v.asIdeal) → w ∈ T') := by
  classical
  -- The set of prime ideals of `𝓞 K` that lie over some prime in `T`.
  set U : Set (Ideal (NumberField.RingOfIntegers K)) :=
    ⋃ v ∈ (T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))),
      Ideal.primesOver v.asIdeal (NumberField.RingOfIntegers K) with hU
  -- It is finite: a finite union of the (finite) sets of primes over each `v`.
  have hUfin : U.Finite := by
    rw [hU]
    exact Set.Finite.biUnion T.finite_toSet
      (fun v _ => IsDedekindDomain.primesOver_finite v.asIdeal (NumberField.RingOfIntegers K))
  -- Transport along the injective map `w ↦ w.asIdeal`.
  have hpre : (IsDedekindDomain.HeightOneSpectrum.asIdeal ⁻¹' U).Finite :=
    Set.Finite.preimage
      (Set.injOn_of_injective IsDedekindDomain.HeightOneSpectrum.asIdeal_injective) hUfin
  refine ⟨hpre.toFinset, ?_, ?_⟩
  · intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    rw [hU] at hw
    simp only [Set.mem_preimage, Set.mem_iUnion] at hw
    obtain ⟨v, hv, hP⟩ := hw
    exact ⟨v, hv, hP.2⟩
  · intro w hw
    rw [Set.Finite.mem_toFinset, hU]
    simp only [Set.mem_preimage, Set.mem_iUnion]
    obtain ⟨v, hv, hLies⟩ := hw
    exact ⟨v, hv, w.isPrime, hLies⟩

end Work.CFTLib.PrimesAbove
