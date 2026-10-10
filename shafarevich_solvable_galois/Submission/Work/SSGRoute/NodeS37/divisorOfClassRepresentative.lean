import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_localNormalise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The divisor of `b · y²` when the ideal class of `A` is represented by a prime

This is the elementary divisor-arithmetic step of the representative normalisation of
Schmidt--Wingberg's p. 16 computation
(`ACTION_claimOfPreTwo_p16_carve_session39.md`, §4.3 and the filed statement
`SSGRoute/NodeS37/exists_coprime_representative`).

If `div(b) = 𝔮 · A²` (in the count form: `count_P(b) = [P = 𝔮] + 2 · count_P(A)`) and the prime
`Q'` represents the ideal class of `A` by an element `y` (`count_P(A) + count_P(y) = [P = Q']`),
then `div(b y²) = 𝔮 · Q'²`.  Consequently `z := b y²` has `supp(z) = {𝔮, Q'}`, so if in addition
`Q' ∉ {ρQ', ρ𝔮}` then `supp(z) ∩ supp(ρz) = ∅` — the coprimality that the `Σ`-step of p. 16 needs.

The two `count` lemmas used are the proved
`Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_mul_unit` and
`Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_pow_unit`.
-/

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute
open scoped Classical

/-- **The divisor of `b y²` when `Q'` represents the class of `A` through `y`.** -/
theorem count_mul_sq_of_classRepresentative {K : Type} [Field K] [NumberField K]
    (𝔮 Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    (b y : Kˣ)
    (hb : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
      = (if P = 𝔮 then 1 else 0) + 2 * FractionalIdeal.count K P A)
    (hy : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P A
        + FractionalIdeal.count K P
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (y : K))
      = (if P = Q' then 1 else 0)) :
    ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          (((b * y ^ 2 : Kˣ) : K)))
      = (if P = 𝔮 then 1 else 0) + 2 * (if P = Q' then 1 else 0) := by
  intro P
  rw [Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_mul_unit (K := K) P b (y ^ 2),
    Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_pow_unit (K := K) P y 2, hb P]
  have h := hy P
  push_cast
  linarith

end Work.SSGRoute.NodeS37
