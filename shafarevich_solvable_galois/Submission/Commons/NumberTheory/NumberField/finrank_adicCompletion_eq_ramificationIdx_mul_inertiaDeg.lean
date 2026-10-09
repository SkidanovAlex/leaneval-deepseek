import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField

noncomputable section

namespace Commons.NumberTheory.NumberField

/-- **Local fundamental identity** `[L_q : K_Q] = e(q|Q) · f(q|Q)` for adic completions of
number fields.

Let `Q` be a prime of the ring of integers of the number field `K`, and let `q` be a prime of
the ring of integers of the number field `L` lying over `Q`.  The extension of adic completions
`q.adicCompletion L` over `Q.adicCompletion K` (via the canonical map
`Commons.RingTheory.Henselian.adicCompletionMap Q q hq`) is a finite extension of local fields of
degree equal to the product of the ramification index and the inertia degree of `q` over `Q`:

`q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K) = finrank (Q.adicCompletion K) (q.adicCompletion L)`.

Proved in the shared commons as
`Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`
(the lower bound `e·f ≤ [L_q : K_Q]` is supplied by lifting an `e·f`-dimensional quotient of the
valuation ring of `L_q`; the upper bound by the matching filtration/level structure on the
completion). -/
theorem finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)).toModule := by
  exact Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
    (K := K) (L := L) Q q hq

end Commons.NumberTheory.NumberField
