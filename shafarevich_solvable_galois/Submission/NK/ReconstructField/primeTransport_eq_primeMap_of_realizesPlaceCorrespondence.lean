import Mathlib
import Submission.NK.ReconstructField.Input
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

/-- Precomposition of valuation subrings with a surjective ring homomorphism is injective. -/
lemma valuationSubring_comap_injective_of_surjective {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (hf : Function.Surjective f) :
    Function.Injective (fun A : ValuationSubring L => A.comap f) := by
  intro A B h
  change A.comap f = B.comap f at h
  ext z
  obtain ⟨x, rfl⟩ := hf z
  have h1 : x ∈ A.comap f ↔ x ∈ B.comap f := by rw [h]
  rwa [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at h1

/-- **The prime compatibility is automatic.**  Let `σ : K₂' ≃+* K₁'` restrict on the embedded base
field to `τ⁻¹` (i.e. `σ (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x` for all `x : K₁`) and
realize the place correspondence `a` of `ϕ` (`RealizesPlaceCorrespondence a σ`).  Then the induced
map on primes is the transport along `τ`: `primeTransport τ 𝔭 = a.primeMap 𝔭` for every prime `𝔭`
of `K₁`.

Proof route: take a place `A` of `K₁'` above `𝔭` (`exists_valuationSubring_at_prime`).  By the
realization, `a.placeMap A = A.comap σ`; its trace on `K₂` is, using
`σ (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x`, the transport `τ(𝔭)`; on the other hand
`a.primeMap_spec` identifies `a.primeMap 𝔭` with the prime below `a.placeMap A`, and
`valuationSubringAtPrime_primeTransport` identifies the valuation subring of `primeTransport τ 𝔭`
with `(valuationSubringAtPrime K₁ 𝔭).comap τ.symm`.  The two valuation subrings agree, and
`valuationSubringAtPrime_injective` finishes.

Consequence: the reconstruction input `ReconstructionInput hϕ a` consists of exactly two
ingredients — a base-field isomorphism `τ : K₁ ≃+* K₂` (the *weak* Neukirch–Uchida theorem) and the
realization of the place map by some Galois twist of a lift of `τ`. -/
theorem primeTransport_eq_primeMap_of_realizesPlaceCorrespondence
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (σ : K₂' ≃+* K₁') {τ : K₁ ≃+* K₂}
    (hbase : ∀ x : K₁, σ (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x)
    (hreal : NK.ReconstructField.RealizesPlaceCorrespondence a σ) :
    ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁,
      NK.Reconstruct.primeTransport τ 𝔭 = a.primeMap 𝔭 := by
  intro 𝔭
  -- a place of `K₁'` above `𝔭`
  set A : NK.Reconstruct.FinitePlaceOf K₁ K₁' :=
    Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') 𝔭 with hA
  have hAspec : A.1.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭 :=
    Submission.NeukirchUchida.placeOver_spec (K₁ := K₁) (K₁' := K₁') 𝔭
  have hprime : Submission.NeukirchUchida.primeOf A.1 A.2 = 𝔭 :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₁) (by
      rw [← Submission.NeukirchUchida.primeOf_spec A.1 A.2, hAspec])
  -- the realizing isomorphism carries the place `A` to `A.comap σ`
  have hplace : (a.placeMap A).1 = A.1.comap (σ : K₂' →+* K₁') := by
    refine valuationSubring_comap_injective_of_surjective (K := K₁') (L := K₂')
      (σ.symm : K₁' →+* K₂') σ.symm.surjective ?_
    change (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') =
      (A.1.comap (σ : K₂' →+* K₁')).comap (σ.symm : K₁' →+* K₂')
    rw [hreal A, NK.Reconstruct.comap_symm_comap_eq σ A.1]
  -- the prime of `K₂` below the image place is `a.primeMap 𝔭`
  have hBspec : (a.placeMap A).1.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ (a.primeMap 𝔭) := by
    rw [← hprime, a.primeMap_spec A]
    exact Submission.NeukirchUchida.primeOf_spec (a.placeMap A).1 (a.placeMap A).2
  -- `σ` restricts to `τ⁻¹` on the base field: the two ring homomorphisms `K₂ →+* K₁'` agree
  have hfun : ((algebraMap K₁ K₁').comp (τ.symm : K₂ →+* K₁)) =
      (σ : K₂' →+* K₁').comp (algebraMap K₂ K₂') := by
    ext y
    simpa using (hbase (τ.symm y)).symm
  -- the two valuation subrings of `K₂` agree
  have key : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂
        (NK.Reconstruct.primeTransport τ 𝔭) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ (a.primeMap 𝔭) := by
    rw [NK.Reconstruct.valuationSubringAtPrime_primeTransport τ 𝔭, ← hAspec, ← hBspec,
      hplace, ValuationSubring.comap_comap, ValuationSubring.comap_comap, hfun]
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₂) key

end NK.ReconstructField
