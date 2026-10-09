import Mathlib.RingTheory.DedekindDomain.AdicValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

theorem algebraMap_mem_valuationSubringAtPrime {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R) (r : R) :
    algebraMap R K r ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rw [Valuation.mem_valuationSubring_iff]
  exact v.valuation_le_one r

end Commons.RingTheory.Valuation