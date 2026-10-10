import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

/-- The `Q.adicCompletion K →+* q.adicCompletion L` map induced by an extension of number
fields `L / K` and a prime `q` of `𝓞 L` lying over the prime `Q` of `𝓞 K` is injective.

Both `Q.adicCompletion K` and `q.adicCompletion L` are fields (completions of a number field at
a nonarchimedean place), and a ring homomorphism from a field into a nontrivial ring has trivial
kernel, hence is injective; indeed a ring homomorphism sends `1` to `1 ≠ 0`, so its kernel is a
proper ideal of a field, which must be `⊥`. -/
theorem adicCompletionMap_injective {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Function.Injective (Commons.RingTheory.Henselian.adicCompletionMap Q q hq) := by
  have : Nontrivial (q.adicCompletion L) := inferInstance
  exact (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).injective

end Commons.NumberTheory.NumberField.Completion
