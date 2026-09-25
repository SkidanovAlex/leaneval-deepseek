import Mathlib
import Submission.NK.BrauerHasse.Commons
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top

universe u

namespace NK.BrauerHasse

theorem exists_heightOneSpectrum_eq_comap {K K' : Type u} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') ≠ ⊤) :
    ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      A.comap (algebraMap K K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 := by
  exact Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap K K')) hA
    (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top (F := K) _ hA)

end NK.BrauerHasse
