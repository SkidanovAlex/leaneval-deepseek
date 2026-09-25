import Mathlib

namespace Work.CFTLib.Transport

open scoped NumberField

/-- The inertia degree of a height one prime of `𝓞 K` in the integral closure is invariant
under a `K`-algebra isomorphism of the number fields. -/
lemma inertiaDegIn_algEquiv_eq {K L L' : Type} [Field K] [Field L] [Field L'] [NumberField K]
    [NumberField L] [NumberField L'] [Algebra K L] [Algebra K L'] [IsGalois K L] [IsGalois K L']
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : L ≃ₐ[K] L') :
    Ideal.inertiaDegIn p.asIdeal (𝓞 L) = Ideal.inertiaDegIn p.asIdeal (𝓞 L') := by
  -- Pick a prime `P` of `𝓞 L` lying over `p`; transport it to `𝓞 L'` along the algebraic
  -- isomorphism induced by `e`.
  obtain ⟨P⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver (𝓞 L)))
  let E : 𝓞 L ≃ₐ[𝓞 K] 𝓞 L' := NumberField.RingOfIntegers.mapAlgEquiv e
  have hmem : P.1.map E ∈ p.asIdeal.primesOver (𝓞 L') := ⟨inferInstance, inferInstance⟩
  haveI hmax : (P.1.map E).IsMaximal := Ideal.isMaximal_of_mem_primesOver hmem
  -- Both `P` and its image have the same inertia degree over `𝓞 K`: their residue fields are
  -- canonically isomorphic over the residue field of `p`.
  have himg : (P.1.map E).inertiaDeg (𝓞 K) = P.1.inertiaDeg (𝓞 K) := by
    have hEq : P.1 = Ideal.comap E (P.1.map E) :=
      (Ideal.comap_map_of_bijective E E.bijective).symm
    letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal P.1
    letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal (P.1.map E)
    rw [Ideal.inertiaDeg_eq p.asIdeal (P.1.map E), Ideal.inertiaDeg_eq p.asIdeal P.1]
    exact (Ideal.residueFieldAlgEquiv' p.asIdeal P.1 (P.1.map E) E hEq).toLinearEquiv.finrank_eq.symm
  -- In a Galois extension the inertia degree of `p` is that of any prime above it.
  rw [Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal P.1 (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal (P.1.map E) (L' ≃ₐ[K] L'), himg]

theorem splitsAt_algEquiv {K L L' : Type} [Field K] [Field L] [Field L'] [NumberField K]
    [NumberField L] [NumberField L'] [Algebra K L] [Algebra K L'] [IsGalois K L] [IsGalois K L']
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (e : L ≃ₐ[K] L') :
    (∀ v ∈ T, Ideal.inertiaDegIn v.asIdeal (NumberField.RingOfIntegers L) = 1) →
      (∀ v ∈ T, Ideal.inertiaDegIn v.asIdeal (NumberField.RingOfIntegers L') = 1) := by
  intro h v hv
  rw [← inertiaDegIn_algEquiv_eq v e]
  exact h v hv

end Work.CFTLib.Transport
