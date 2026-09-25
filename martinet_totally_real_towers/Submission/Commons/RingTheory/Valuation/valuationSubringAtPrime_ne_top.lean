import Mathlib.RingTheory.DedekindDomain.AdicValuation

namespace Commons.RingTheory.Valuation

open IsDedekindDomain

theorem valuationSubringAtPrime_ne_top {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v ≠ ⊤ := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
  infer_instance

end Commons.RingTheory.Valuation