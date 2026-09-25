import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
import Submission.Commons.NumberTheory.RamificationInertia.exists_map_galRestrict_eq

namespace Commons.NumberTheory.RamificationInertia

open scoped Pointwise

/-- **The Galois action on places, in valuation ring form.**  If `q'` is the prime of `𝓞 L`
obtained from the prime `q` by applying the automorphism `σ` (via the induced automorphism
`galRestrict` of `𝓞 L`), then the pointwise image under `σ` of the valuation ring `𝒪_{L,q}`
is the valuation ring `𝒪_{L,q'}`.

This is the place-by-place compatibility of the Galois action on primes with the Galois action
on the corresponding valuation subrings; it reduces to the elementwise statement that
`x ∈ 𝒪_{L,q}` iff `σ x ∈ 𝒪_{L,q'}`. -/
theorem smul_valuationSubringAtPrime_eq_map_galRestrict {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (q q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[K] L)
    (h : q'.asIdeal = q.asIdeal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ)) :
    σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L q =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L q' := by
  set f := galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ
    with hf
  -- `key1` and `key2` express membership in `q.asIdeal.map f` in terms of membership in
  -- `q.asIdeal`, using that `f` is a bijection.
  have key1 : ∀ x : NumberField.RingOfIntegers L, f x ∈ q.asIdeal.map f ↔ x ∈ q.asIdeal := by
    intro x
    rw [Ideal.mem_map_iff_of_surjective f f.surjective]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← f.injective hyx]
    · exact fun hx => ⟨x, hx, rfl⟩
  have key2 : ∀ z : NumberField.RingOfIntegers L,
      z ∈ q.asIdeal.map f ↔ f.symm z ∈ q.asIdeal := by
    intro z
    rw [Ideal.mem_map_iff_of_surjective f f.surjective]
    constructor
    · rintro ⟨y, hy, hyz⟩
      rw [← hyz, f.symm_apply_apply]
      exact hy
    · exact fun hz => ⟨f.symm z, hz, f.apply_symm_apply z⟩
  have hf_symm : f.symm = galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ⁻¹ := by
    rw [hf]
    exact (MulEquiv.map_inv (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)) σ).symm
  -- Unfold both sides into statements about the localizations.
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    Commons.RingTheory.Valuation.mem_valuationSubringAtPrime,
    Commons.RingTheory.Valuation.mem_valuationSubringAtPrime,
    AlgEquiv.smul_def]
  constructor
  · -- `σ⁻¹ y ∈ 𝒪_{L,q}` gives `y = σ a / σ s` with `σ s ∉ q'`.
    rintro ⟨a, s, hs, hys⟩
    refine ⟨f a, f s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff, h, key1 s]
      exact Ideal.mem_primeCompl_iff.mp hs
    · have hys' : y = σ (algebraMap (NumberField.RingOfIntegers L) L a *
          (algebraMap (NumberField.RingOfIntegers L) L s)⁻¹) := by
        rw [← hys]
        exact (AlgEquiv.apply_symm_apply σ y).symm
      rw [hys', map_mul, map_inv₀]
      simp only [hf, algebraMap_galRestrict_apply]
  · -- `y = a / s` with `s ∉ q'` gives `σ⁻¹ y = f⁻¹ a / f⁻¹ s` with `f⁻¹ s ∉ q`.
    rintro ⟨a, s, hs, hys⟩
    refine ⟨f.symm a, f.symm s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff, ← key2 s, ← h]
      exact Ideal.mem_primeCompl_iff.mp hs
    · rw [hf_symm, algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
      have hys' : σ⁻¹ y = σ⁻¹ (algebraMap (NumberField.RingOfIntegers L) L a *
          (algebraMap (NumberField.RingOfIntegers L) L s)⁻¹) := by
        rw [hys]
      rw [hys', map_mul, map_inv₀]

/-- **Transitivity of the Galois action on the places over a fixed place, in valuation ring
form.**  For `L/K` a finite Galois extension of number fields and `w₁`, `w₂` places of `L`
lying over the same place `p` of `K`, there is `σ : L ≃ₐ[K] L` carrying the valuation ring of
`w₁` onto the valuation ring of `w₂`. -/
theorem exists_smul_valuationSubringAtPrime_eq {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₁ w₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [w₁.asIdeal.LiesOver p.asIdeal] [w₂.asIdeal.LiesOver p.asIdeal] :
    ∃ σ : L ≃ₐ[K] L,
      σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w₁ =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w₂ := by
  -- Transitivity of the action on the primes above `p`, in `map` form.
  obtain ⟨σ, hσ⟩ := exists_map_galRestrict_eq p w₁ w₂
  exact ⟨σ, smul_valuationSubringAtPrime_eq_map_galRestrict w₁ w₂ σ hσ.symm⟩

end Commons.NumberTheory.RamificationInertia
