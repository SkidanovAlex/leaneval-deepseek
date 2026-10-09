import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Norm.Basic
import Submission.Commons.RingTheory.Henselian.valuation_completion_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Henselian

set_option linter.style.haveILetI false

open scoped NumberField Valued WithZero

/-- **The map between adic completions shrinks the open unit ball into the open unit ball**: for
number fields `K ⊆ L`, a height-one prime `Q` of `𝓞 K` and a height-one prime `q` of `𝓞 L`
lying over `Q`, if `x` is an element of the integer ring `Q.adicCompletionIntegers K` of the
completion of `K` with `Valued.v x < 1` (i.e. `x` lies in the maximal ideal), then the image of
`x` under `adicCompletionMap Q q hq` has `Valued.v < 1` (it lies in the maximal ideal of
`q.adicCompletionIntegers L`).

Proof strategy: use `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` on elements `y` of `K`
(`v_q y = (v_Q y) ^ e`, so `v_Q y < 1` implies `v_q y ≤ exp (-e) < 1`), the density of `K` in its
completion, the openness of the open unit ball, the closedness of the closed unit ball
`{v ≤ exp (-1)}`, continuity of `adicCompletionMap`
(`Commons.RingTheory.Henselian.adicCompletionMap_continuous`) and of the valuation -- the same
pattern as `Commons.RingTheory.Henselian.adicCompletionMap_mem_integers`.  The key algebraic
input is `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`. -/
theorem adicCompletionMap_val_lt_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    {x : Q.adicCompletionIntegers K}
    (hx : Valued.v (x : Q.adicCompletion K) < 1) :
    Valued.v (Commons.RingTheory.Henselian.adicCompletionMap Q q hq
      (x : Q.adicCompletion K)) < 1 := by
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  -- the explicit formula `v_q (adicCompletionMap x) = (v_Q x) ^ e` for every element of the
  -- completion of `K`, where `e` is the ramification index
  rw [valuation_completion_liesOver Q q hq (x : Q.adicCompletion K)]
  -- the ramification index is nonzero, hence at least one
  have he : Q.asIdeal.ramificationIdx' q.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q.asIdeal Q.ne_bot
  exact pow_lt_one₀ (zero_le) hx he

end Commons.RingTheory.Henselian