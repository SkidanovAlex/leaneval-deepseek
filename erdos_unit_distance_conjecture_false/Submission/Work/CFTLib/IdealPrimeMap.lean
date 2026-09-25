import Mathlib

/-!
# Transporting a height-one prime along a ring equivalence

For a Dedekind domain `R` and a ring equivalence `e : R ≃+* R`, the height-one primes of `R` are
permuted: the prime `e⁻¹ w` has underlying ideal `w.asIdeal.comap e`, equivalently
`Ideal.map e.symm w.asIdeal`.  This file introduces that transport, `Work.CFTLib.primeMap`,
together with its elementary properties.  It is used to state the compatibility of
`FractionalIdeal.count` with the transport of fractional ideals along `e`.
-/

open scoped nonZeroDivisors

namespace Work.CFTLib

/-- The prime `e⁻¹ w` of `R` obtained from the prime `w` by transporting along the ring
equivalence `e : R ≃+* R`: its underlying ideal is `w.asIdeal.comap e`. -/
noncomputable def primeMap {R : Type*} [CommRing R] [IsDedekindDomain R] (e : R ≃+* R)
    (w : IsDedekindDomain.HeightOneSpectrum R) : IsDedekindDomain.HeightOneSpectrum R :=
  ⟨w.asIdeal.comap (e : R →+* R), inferInstance,
    fun h => w.ne_bot (Ideal.comap_injective_of_surjective (f := (e : R →+* R)) e.surjective
      (h.trans (Ideal.comap_bot_of_injective (f := (e : R →+* R)) e.injective).symm))⟩

@[simp] theorem primeMap_asIdeal {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (w : IsDedekindDomain.HeightOneSpectrum R) :
    (primeMap e w).asIdeal = w.asIdeal.comap (e : R →+* R) := rfl

/-- The underlying ideal of `primeMap e w` is also `Ideal.map e.symm w.asIdeal`. -/
theorem primeMap_asIdeal_map {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (w : IsDedekindDomain.HeightOneSpectrum R) :
    (primeMap e w).asIdeal = Ideal.map (e.symm : R ≃+* R) w.asIdeal := by
  rw [primeMap_asIdeal]
  exact (Ideal.map_symm (I := w.asIdeal) e).symm

/-- Transporting a prime along `e.symm` and then along `e` is the identity. -/
@[simp] theorem primeMap_symm_primeMap {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (w : IsDedekindDomain.HeightOneSpectrum R) :
    primeMap e (primeMap e.symm w) = w := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [primeMap_asIdeal, primeMap_asIdeal, Ideal.comap_comap,
    show (e.symm : R →+* R).comp (e : R →+* R) = RingHom.id R from by ext x; simp,
    Ideal.comap_id]

end Work.CFTLib
