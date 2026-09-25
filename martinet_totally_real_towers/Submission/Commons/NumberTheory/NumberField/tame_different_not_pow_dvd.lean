import Submission.Commons.NumberTheory.NumberField.tame_different

open scoped NumberField

namespace Commons.NumberTheory.NumberField

/-
The tame different-ideal statement: if a prime ideal `P` of the ring of integers of a number
field `K` lies over the rational prime `p` and is *tame* over `p` (i.e. `p ∤ e`, where
`e := P.ramificationIdx ℤ` is the ramification index), then `P^e` does not divide the
different ideal `differentIdeal ℤ (𝓞 K)`.

This is the tame half of Dedekind's different theorem: for a tame prime the exponent of `P`
in the different is exactly `e − 1` (the free lower bound `P^(e−1) ∣ differentIdeal` is
`Ideal.pow_sub_one_dvd_differentIdeal`); here we only need the resulting non-divisibility by
`P^e`.  The full proof (a trace/flag argument over the quotient `𝓞 K ⧸ P^e`, isolating a
trace witness `y` in the complementary factor `Q` of the splitting
`(p) = P^e · Q` whose integer trace is not divisible by `p`) is developed in the shared
commons module `Submission.Commons.NumberTheory.NumberField.tame_different`.
-/
theorem tame_different_not_pow_dvd {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (NumberField.RingOfIntegers K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (htame : ¬ p ∣ P.ramificationIdx ℤ) :
    ¬ P ^ P.ramificationIdx ℤ ∣ differentIdeal ℤ (NumberField.RingOfIntegers K) := by
  exact tame_different (K := K) p P htame

end Commons.NumberTheory.NumberField
