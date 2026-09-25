import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Commons.RingTheory.Henselian.valuation_completion_liesOver

/-!
# The valuation of the image of an element under the map of adic completions

For an extension `L / K` of number fields, a height-one prime `Q` of `𝓞 K` and a height-one
prime `q` of `𝓞 L` lying over `Q`, the induced ring homomorphism

`Commons.RingTheory.Henselian.adicCompletionMap Q q hq : Q.adicCompletion K →+* q.adicCompletion L`

of adic completions satisfies

`v (adicCompletionMap Q q hq x) = (v x) ^ e`

for every `x : Q.adicCompletion K`, where `e = q.asIdeal.ramificationIdx (𝓞 K)` is the
ramification index of `q` over `Q`.

This is the statement of `Commons.RingTheory.Henselian.valuation_completion_liesOver`, which
expresses the exponent as `Q.asIdeal.ramificationIdx' q.asIdeal`; the only additional input here
is the identification `Q.asIdeal.ramificationIdx' q.asIdeal = q.asIdeal.ramificationIdx (𝓞 K)`
of the two (equivalent) definitions of the ramification index in Mathlib
(`Ideal.ramificationIdx'_eq_ramificationIdx`).
-/

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

theorem val_adicCompletionMap_eq_pow {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : Q.adicCompletion K) :
    Valued.v (Commons.RingTheory.Henselian.adicCompletionMap Q q hq x) =
      (Valued.v x) ^ (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) := by
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  have hram : Q.asIdeal.ramificationIdx' q.asIdeal =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
    Ideal.ramificationIdx'_eq_ramificationIdx (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers L) (p := Q.asIdeal) (q := q.asIdeal) Q.ne_bot
  rw [Commons.RingTheory.Henselian.valuation_completion_liesOver Q q hq x, hram]

end Commons.NumberTheory.NumberField.Completion