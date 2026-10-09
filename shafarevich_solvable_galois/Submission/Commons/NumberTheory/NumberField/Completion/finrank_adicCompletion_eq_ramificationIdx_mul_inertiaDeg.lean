import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

/-- The local fundamental identity for adic completions of number fields: if `q` is a prime of
`𝓞 L` lying over the prime `Q` of `𝓞 K`, then the extension of adic completions `L_q / K_Q` has
degree equal to the product of the ramification index and the inertia degree of `q` over `K`:

`Module.finrank (Q.adicCompletion K) (q.adicCompletion L) = e · f`

where the module structure on `q.adicCompletion L` over `Q.adicCompletion K` is the one induced by
the continuous algebra map `Commons.RingTheory.Henselian.adicCompletionMap Q q hq`, `e` is the
ramification index `q.asIdeal.ramificationIdx (𝓞 K)` and `f` the inertia degree
`q.asIdeal.inertiaDeg (𝓞 K)`.

This is the classical identity `[L_w : K_v] = e_w · f_w` for a finite extension of number fields,
proved locally: it follows by combining (a) the lower bound `e·f ≤ finrank` obtained from the
residue-field/valuation structure of the completed valuation rings (an `e·f`-dimensional quotient
of the valuation ring of `L_q` injects, via lifting, into `L_q` as a `K_Q`-vector space), and
(b) the matching upper bound.  -/
theorem finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)).toModule := by
  exact Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg_aux Q q hq

end Commons.NumberTheory.NumberField.Completion
