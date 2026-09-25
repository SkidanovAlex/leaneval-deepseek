import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.sumFinrank_completions_eq_finrank

namespace Commons.NumberTheory.NumberField.Completion

/-- **The sum of local degrees equals the global degree.**

For a finite extension `L / K` of number fields and a prime `Q` of `𝓞 K`, summing over all
primes `q` of `𝓞 L` lying over `Q` the degree `[L_q : K_Q]` of the extension of `q`-adic and
`Q`-adic completions gives the global degree `[L : K]`:

`∑_{q | Q} [L_q : K_Q] = [L : K]`,

where each `L_q = (e qq).adicCompletion L` carries the `K_Q = Q.adicCompletion K`-module
structure induced by the continuous algebra map
`Commons.RingTheory.Henselian.adicCompletionMap Q (e qq) qq.2.2` (extending `algebraMap K L`).

This is the global avatar of the local fundamental identity `[L_q : K_Q] = e_q · f_q`
(`Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`):
combined with the global fundamental identity `∑_{q | Q} e_q · f_q = [L : K]`
(`Ideal.sum_ramification_inertia_eq_finrank`) the two identities agree termwise; see
`sumFinrank_completions_eq_finrank`. -/
theorem sum_finrank_adicCompletion_eq_finrank
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    let e : Q.asIdeal.primesOver (NumberField.RingOfIntegers L) →
        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
      fun qq => IsDedekindDomain.HeightOneSpectrum.mk qq.1 qq.2.1
        (Ideal.ne_bot_of_mem_primesOver (A := NumberField.RingOfIntegers K)
          (B := NumberField.RingOfIntegers L) Q.ne_bot qq.2)
    (∑ qq : Q.asIdeal.primesOver (NumberField.RingOfIntegers L),
        @Module.finrank (Q.adicCompletion K) ((e qq).adicCompletion L) _ _
          (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q (e qq) qq.2.2)).toModule) =
      Module.finrank K L := by
  simpa using (sumFinrank_completions_eq_finrank (K := K) (L := L) Q)

end Commons.NumberTheory.NumberField.Completion
