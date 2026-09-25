import Mathlib.RingTheory.DedekindDomain.AdicValuation

namespace Commons.RingTheory.Valuation

theorem algebraMap_mem_valuationSubringAtPrime {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R) (r : R) :
    algebraMap R K r ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rw [Valuation.mem_valuationSubring_iff]
  exact v.valuation_le_one r

end Commons.RingTheory.Valuation