import Mathlib
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one

namespace Commons.NumberTheory.NumberField.Completion

theorem exists_uniformizer_val_eq_exp_neg_one {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ π : v.adicCompletionIntegers K,
      Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) ∧
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π} := by
  refine ⟨Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K) (K := K) v,
    ?_, ?_⟩
  · exact Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) v
  · exact Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer
      (R := NumberField.RingOfIntegers K) (K := K) v

end Commons.NumberTheory.NumberField.Completion
