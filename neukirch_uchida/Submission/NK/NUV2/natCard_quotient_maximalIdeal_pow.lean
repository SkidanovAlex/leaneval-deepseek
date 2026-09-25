import Mathlib
import Submission.NK.NUV2.BC2Imports

set_option linter.style.haveILetI false

open scoped NumberField

namespace NK.NUV2

/-- Let `A = q.adicCompletionIntegers K`, `e = q.asIdeal.ramificationIdx ℤ`,
`f = q.asIdeal.inertiaDeg ℤ`, with `q` lying over `(2)`.  The quotient of `A` by the `e`-th power
of its maximal ideal has `2 ^ (e * f)` elements.
Proof sketch: `A ⧸ m ^ e ≃ 𝓞 K ⧸ q ^ e`
(`Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv`),
`Nat.card (𝓞 K ⧸ q ^ e) = (Nat.card (𝓞 K ⧸ q)) ^ e` (`Submodule.cardQuot_pow_of_prime` with
`Submodule.cardQuot_apply`), and `Nat.card (𝓞 K ⧸ q) = 2 ^ f` since
`f = Module.finrank (ℤ ⧸ Ideal.span {(2:ℤ)}) (𝓞 K ⧸ q.asIdeal)` by
`Ideal.inertiaDeg_eq_of_isMaximal` and `Nat.card (ℤ ⧸ Ideal.span {(2:ℤ)}) = 2`
(`Module.natCard_eq_pow_finrank`, `Int.quotientSpanNatEquivZMod`, `Nat.card_zmod`). -/
theorem natCard_quotient_maximalIdeal_pow (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hlies : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})) :
    Nat.card (q.adicCompletionIntegers K ⧸
        (IsLocalRing.maximalIdeal (q.adicCompletionIntegers K)) ^
          (q.asIdeal.ramificationIdx ℤ)) =
      2 ^ (q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ) := by
  classical
  haveI hprime : q.asIdeal.IsPrime := q.isPrime
  haveI hlie : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) := hlies
  -- Step 1: the quotient of the completion by `𝔪 ^ e` is the quotient of `𝓞 K` by `q ^ e`.
  have h1 : Nat.card (q.adicCompletionIntegers K ⧸
        (IsLocalRing.maximalIdeal (q.adicCompletionIntegers K)) ^
          (q.asIdeal.ramificationIdx ℤ)) =
      Nat.card ((NumberField.RingOfIntegers K) ⧸
        q.asIdeal ^ (q.asIdeal.ramificationIdx ℤ)) := by
    obtain ⟨φ, -⟩ :=
      Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv
        (K := K) q (q.asIdeal.ramificationIdx ℤ)
    exact (Nat.card_congr φ.toEquiv).symm
  -- Step 2: `#(𝓞 K ⧸ q ^ e) = (#(𝓞 K ⧸ q)) ^ e`.
  have h2 : Nat.card ((NumberField.RingOfIntegers K) ⧸
        q.asIdeal ^ (q.asIdeal.ramificationIdx ℤ)) =
      (Nat.card ((NumberField.RingOfIntegers K) ⧸ q.asIdeal)) ^
        (q.asIdeal.ramificationIdx ℤ) := by
    rw [← Submodule.cardQuot_apply (S := q.asIdeal ^ q.asIdeal.ramificationIdx ℤ),
      ← Submodule.cardQuot_apply (S := q.asIdeal)]
    exact cardQuot_pow_of_prime q.ne_bot (i := q.asIdeal.ramificationIdx ℤ)
  -- Step 3: `#(𝓞 K ⧸ q) = 2 ^ f`, since `q` lies over `(2)`.
  have h3 : Nat.card ((NumberField.RingOfIntegers K) ⧸ q.asIdeal) =
      2 ^ q.asIdeal.inertiaDeg ℤ := by
    rw [← Submodule.cardQuot_apply (S := q.asIdeal), ← Ideal.absNorm_apply q.asIdeal]
    exact (Ideal.pow_inertiaDeg (R := NumberField.RingOfIntegers K) 2 q.asIdeal).symm
  have h4 : q.asIdeal.inertiaDeg ℤ * q.asIdeal.ramificationIdx ℤ =
      q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ := Nat.mul_comm _ _
  rw [h1, h2, h3, ← pow_mul, h4]

end NK.NUV2
