import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers

/-!
# The closure of the image of the local integers is the ring of integers of the completion

For a number field `K` and a non-zero prime ideal `p` of `𝓞 K`, the image in the `p`-adic
completion `K_p` of the local ring `{c : K | v_p c ≤ 1}` is dense in the valuation ring
`p.adicCompletionIntegers K` of the completion, so its closure *is* that valuation ring.

The two inclusions are:

* the image consists of integral elements (the valuation of the completion extends the `p`-adic
  valuation of `K`), and `p.adicCompletionIntegers K` is closed as a valuation subring of a
  valued field;
* conversely, the closure of the image of `𝓞 K` (which is contained in that of
  `{c : K | v_p c ≤ 1}`) is all of `p.adicCompletionIntegers K`, by
  `Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers`.
-/

open scoped NumberField
open IsDedekindDomain

namespace NK.NeukirchUchida

theorem closure_algebraMap_le_one_eq_adicCompletionIntegers {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    closure ((algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)) ''
        {c : K | IsDedekindDomain.HeightOneSpectrum.valuation K p c ≤ 1}) =
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p :
        Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)) := by
  refine Set.Subset.antisymm ?_ ?_
  · refine closure_minimal ?_ (Valued.isClosed_valuationSubring (p.adicCompletion K))
    rintro y ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe]
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K)]
    rw [show algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c
        = (c : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) from rfl]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hc
  · intro x hx
    have hdense := Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
      K p ⟨x, hx⟩
    refine closure_mono ?_ hdense
    rintro y ⟨r, rfl⟩
    exact ⟨(r : K), IsDedekindDomain.HeightOneSpectrum.valuation_le_one p r, rfl⟩

end NK.NeukirchUchida
