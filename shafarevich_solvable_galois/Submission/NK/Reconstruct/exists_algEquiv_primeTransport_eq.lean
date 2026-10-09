import Mathlib
import Submission.NK.Reconstruct.Transport
import Submission.NK.Reconstruct.exists_frobElement
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois group acts transitively on the primes above a fixed prime

For a finite normal (hence Galois, over `ℚ`) number field `L/ℚ` and two primes `P`, `Q` of `𝓞 L`
lying over the same prime `p` of `ℤ`, there is a Galois automorphism `σ : Gal(L/ℚ)` carrying `P`
to `Q`:

`NK.Reconstruct.exists_algEquiv_primeTransport_eq`.

This is the transport form of the transitivity of the Galois action on the primes above `p`
(`NK.Reconstruct.exists_smul_eq_of_liesOver`), made possible by the comparison
`NK.Reconstruct.primeTransport_toRingEquiv_eq_smul` between the transport of primes along a
Galois automorphism and its action on primes.
-/

set_option linter.style.haveILetI false

namespace NK.Reconstruct

open scoped Pointwise

/-- **The transport of primes along a Galois automorphism is its action on primes.**

The isomorphism of rings of integers induced by `σ : Gal(L/K)` is the restriction `galRestrict`
of `σ`, so the primes are transported in the same way. -/
lemma primeTransport_toRingEquiv_eq_smul {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (σ : Gal(L/K))
    (P : NK.Chebotarev.PrimeIdeal L) :
    NK.Reconstruct.primeTransport (σ : L ≃+* L) P = σ • P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NK.Chebotarev.smul_primeIdeal_asIdeal]
  show Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv (σ : L ≃+* L) :
      NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)) P.asIdeal =
    Ideal.map ((galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ :
      NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)) P.asIdeal
  rw [show (NK.Reconstruct.ringOfIntegersEquiv (σ : L ≃+* L) :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) =
      (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) from by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    show ((NK.Reconstruct.ringOfIntegersEquiv (σ : L ≃+* L) x :
        NumberField.RingOfIntegers L) : L) =
      ((galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ x : NumberField.RingOfIntegers L) : L)
    rw [NK.Reconstruct.ringOfIntegersEquiv_apply]
    exact (algebraMap_galRestrict_apply (NumberField.RingOfIntegers K) σ x).symm]

/-- **Transitivity of the Galois action on the primes above a fixed prime, in transport form.**

For a finite normal number field `L/ℚ`, any two primes of `𝓞 L` above a fixed prime `p` of `ℤ`
are related by a Galois automorphism of `L/ℚ`.  (Normality is upgraded to Galois-ness using that
`ℚ` has characteristic zero.) -/
theorem exists_algEquiv_primeTransport_eq {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    {L : IntermediateField ℚ Ω} [FiniteDimensional ℚ L] [Normal ℚ L] [NumberField ↥L]
    {p : NK.Chebotarev.PrimeIdeal ℚ} {P Q : NK.Chebotarev.PrimeIdeal ↥L}
    (hP : P.asIdeal.LiesOver p.asIdeal) (hQ : Q.asIdeal.LiesOver p.asIdeal) :
    ∃ σ : Gal(↥L/ℚ), NK.Reconstruct.primeTransport (σ : ↥L ≃+* ↥L) P = Q := by
  haveI : IsGalois ℚ ↥L := IsGalois.mk
  obtain ⟨σ, hσ⟩ := NK.Reconstruct.exists_smul_eq_of_liesOver (K := ℚ) (L := ↥L) hP hQ
  exact ⟨σ, by rw [primeTransport_toRingEquiv_eq_smul, hσ]⟩

end NK.Reconstruct
