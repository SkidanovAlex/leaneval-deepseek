import Mathlib.RingTheory.DedekindDomain.AdicValuation

namespace Commons.NumberTheory.NumberField

open IsDedekindDomain

/-- The `v`-adic valuation of the image of `x : K` under the canonical embedding
`K → v.adicCompletion K` equals the global `v`-adic valuation of `x`.

This is the statement that the completion's valuation restricts to the valuation on `K`. -/
theorem val_algebraMap_adicCompletion_eq {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) :
    Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap K (v.adicCompletion K) x) = v.valuation K x := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply]
  convert IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (R := NumberField.RingOfIntegers K) (K := K) v x using 2

end Commons.NumberTheory.NumberField