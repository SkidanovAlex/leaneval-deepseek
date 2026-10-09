import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The adic-completion map sends the ring of integers into the ring of integers

This is the version of `Commons.RingTheory.Henselian.adicCompletionMap_mem_integers`
(the ring homomorphism between adic completions induced by a prime `q` of `𝓞 L` lying over a
prime `Q` of `𝓞 K` maps `Q.adicCompletionIntegers K` into `q.adicCompletionIntegers L`)
registered under the name `adicCompletionMap_mem_integers_of_integers`.
-/

open scoped NumberField

noncomputable section

namespace Commons.RingTheory.Henselian

theorem adicCompletionMap_mem_integers_of_integers
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    {x : Q.adicCompletion K}
    (hx : x ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K))) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq x ∈
      (q.adicCompletionIntegers L : Set (q.adicCompletion L)) := by
  exact adicCompletionMap_mem_integers Q q hq hx

end Commons.RingTheory.Henselian
