import Mathlib
import Submission.NK.ReconstructField.All

namespace NK.ReconstructField

/-- **The prime below the place transported by a `MapsBase` isomorphism.**
Let `σ : K₂' ≃+* K₁'` map the embedded copy of `K₂` onto the embedded copy of `K₁` and restrict on
the base field to `τ⁻¹` (i.e. `σ (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x`).  Then for a
place `A` of `K₁'` over a finite prime of `K₁`, the prime of `𝓞 K₂` below the place `A.comap σ` of
`K₂'` is the transport along `τ` of the prime of `𝓞 K₁` below `A`.

Both primes are described by their valuation subrings (`primeOf_spec`), and the valuation subring
of a transported prime is the transform of the valuation subring
(`valuationSubringAtPrime_primeTransport`); the identity `σ (algebraMap K₂ K₂' (τ x)) =
algebraMap K₁ K₁' x` is exactly the statement that the two ring homomorphisms
`(algebraMap K₁ K₁').comp τ.symm` and `σ.comp (algebraMap K₂ K₂')` agree. -/
theorem primeOf_comap_eq_primeTransport
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {τ : K₁ ≃+* K₂} {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hbase : ∀ x : K₁, σ (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x)
    (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') :
    Submission.NeukirchUchida.primeOf (A.1.comap (σ : K₂' →+* K₁'))
        (NK.Reconstruct.comap_sigma_comap_ne_top hσ A.2) =
      NK.Reconstruct.primeTransport τ (Submission.NeukirchUchida.primeOf A.1 A.2) := by
  -- both primes are determined by the valuation subring of `K₂` attached to them
  refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₂) ?_
  -- `σ` restricts to `τ⁻¹` on the base field: the two ring homomorphisms `K₂ →+* K₁'` agree
  have hfun : ((algebraMap K₁ K₁').comp (τ.symm : K₂ →+* K₁)) =
      (σ : K₂' →+* K₁').comp (algebraMap K₂ K₂') := by
    ext y
    simpa using (hbase (τ.symm y)).symm
  rw [← Submission.NeukirchUchida.primeOf_spec (K₁ := K₂) (K₁' := K₂')
        (A.1.comap (σ : K₂' →+* K₁')) (NK.Reconstruct.comap_sigma_comap_ne_top hσ A.2),
      NK.Reconstruct.valuationSubringAtPrime_primeTransport τ
        (Submission.NeukirchUchida.primeOf A.1 A.2),
      ← Submission.NeukirchUchida.primeOf_spec (K₁ := K₁) (K₁' := K₁') A.1 A.2,
      ValuationSubring.comap_comap, ValuationSubring.comap_comap, hfun]

end NK.ReconstructField
