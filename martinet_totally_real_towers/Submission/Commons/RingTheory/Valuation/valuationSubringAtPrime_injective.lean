import Mathlib.RingTheory.DedekindDomain.AdicValuation

namespace Commons.RingTheory.Valuation

theorem valuationSubringAtPrime_injective {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Injective (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (R := R) K) := by
  intro p q hpq
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
  rw [Valuation.isEquiv_iff_valuationSubring]
  rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := K),
    ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := K)]
  exact hpq

end Commons.RingTheory.Valuation