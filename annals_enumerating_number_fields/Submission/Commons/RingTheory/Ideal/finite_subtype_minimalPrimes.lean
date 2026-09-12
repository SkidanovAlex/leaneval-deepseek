import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

namespace Commons.RingTheory.Ideal

theorem finite_subtype_minimalPrimes {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Finite {p : Ideal R // p ∈ I.minimalPrimes} :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing R I).to_subtype

end Commons.RingTheory.Ideal
