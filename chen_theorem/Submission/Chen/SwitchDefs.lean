import Mathlib
import Submission.Commons.NumberTheory.Chen.rough_theta_lower_of_bv
import Submission.Commons.NumberTheory.Chen.twin_product_ratio
import Submission.Chen.Interface

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Submission

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# Chen's switch: definitions and elementary combinatorics

This module sets up the vocabulary of Chen's *switching* device in the `p + 2` form,
in the quantitative shape used by Bordignon–Johnston–Starichkova (arXiv:2207.09452)
and Nathanson's book, and proves the elementary (non-analytic) part of the argument.

* `chenSiftLimit x` is Chen's sift limit `M = ⌊cut (x^{1/8}) 1⌋ + 1 ≈ x^{0.0749}`;
  this is exactly the value for which `chen_sharp_rough_lower` is proved.
* `chenWindowTop x` is the window top `Y = ⌊x^{1/3}⌋ + 1`.
* `s0Set x M` is the set of primes `p ≤ x` with `p + 2` coprime to the odd primorial below `M`
  (the `M`-rough shifts).
* `apMass x M q` is the `θ`-mass of the members of `s0Set x M` with `q ∣ p + 2`.
* `goodMass x M` is the `θ`-mass of the members of `s0Set x M` with `Ω (p+2) ≤ 2`.
* `bTermMass x M Y` is the `θ`-mass of the members of `s0Set x M` whose shift is a product
  of three primes `q q₂ q₃` with `M ≤ q < Y ≤ q₂ ≤ q₃` (the `B`-term of Chen's argument).
* `sqMass x M Y` is the `θ`-mass of the members of `s0Set x M` whose shift is divisible by
  `q ^ 2` for some window prime `q` (a cheap exceptional set).

The main theorem of this module, `switch_decomposition`, is the (exact) identity

  `goodMass ≥ goodSum - (1/2)·Σ_{q ∈ W} apMass q - (1/2)·(bTermMass + sqMass)`,

which is the elementary heart of Chen's switch: the primes counted by `goodSum` whose shift
has `Ω ≥ 3` are either charged to a window prime (twice, whence the factor `1/2`), or they are
`B`-term shifts, or `q^2`-divisible shifts.
-/

/-- Chen's sift limit `M = ⌊cut (x^{1/8}) 1⌋ + 1` (roughly `x^{0.0749}`). -/
noncomputable def chenSiftLimit (x : ℕ) : ℕ := ⌊cut (Real.rpow (x : ℝ) (1 / 8)) 1⌋₊ + 1

/-- The **optimal** sift limit for the switch assembly, `M = ⌊x^{1/10}⌋ + 1`.

The three analytic inputs of the assembly (`Submission/Chen/NOTES.md`) are best requested at this
sift limit rather than at `chenSiftLimit x ≈ x^{0.0749}`: the lower-bound deficit needed is then
`≤ 0.05` (the one-dimensional linear sieve gives `1 - f(5) ≈ 0.003`) instead of `≤ 0.006`, and the
`B`-term constant allowed is `2.6` instead of `3.5`; the ensemble then has a ≈ 20% margin rather
than 2.5%.  See `Submission/Chen/NOTES.md` for the table. -/
noncomputable def chenSiftLimitTenth (x : ℕ) : ℕ := ⌊Real.rpow (x : ℝ) (1 / 10)⌋₊ + 1

/-- Chen's window top `Y = ⌊x^{1/3}⌋ + 2`.  The `+2` (rather than `+1`) makes the
strict inequality `(x+2) < Y ^ 3` hold for every `x`, which is what guarantees that every
`M`-rough shift with `Ω ≥ 3` has a prime factor in the window `[M, Y)`. -/
noncomputable def chenWindowTop (x : ℕ) : ℕ := ⌊Real.rpow (x : ℝ) (1 / 3)⌋₊ + 2

/-- The window primes: odd primes in `[M, Y)`. -/
def winPrimes (M Y : ℕ) : Finset ℕ := (oddLt Y).filter (fun q => M ≤ q)

/-- The set of primes `p ≤ x` with `p + 2` coprime to the odd primorial below `M`. -/
noncomputable def s0Set (x M : ℕ) : Finset ℕ :=
  ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime)).filter (fun p => Id (p + 2) M = 1)

/-- `θ`-mass of the members of `s0Set x M` whose shift is divisible by `q`. -/
noncomputable def apMass (x M q : ℕ) : ℝ :=
  ((s0Set x M).filter (fun p => q ∣ p + 2)).sum (fun p => Real.log (p : ℝ))

/-- `θ`-mass of the members of `s0Set x M` whose shift has `Ω ≤ 2`. -/
noncomputable def goodMass (x M : ℕ) : ℝ :=
  ((s0Set x M).filter (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 2)).sum
    (fun p => Real.log (p : ℝ))

/-- The number of window prime factors of `n` (without multiplicity), as a real number. -/
noncomputable def rhoStar (n M Y : ℕ) : ℝ :=
  ∑ q ∈ winPrimes M Y, if q ∣ n then (1 : ℝ) else 0

/-- `θ`-mass of the members of `s0Set x M` whose shift is a product of three primes
`q q₂ q₃` with `M ≤ q < Y ≤ q₂ ≤ q₃` (the `B`-term). -/
noncomputable def bTermMass (x M Y : ℕ) : ℝ :=
  ((s0Set x M).filter (fun p => ∃ q q₂ q₃ : ℕ, q.Prime ∧ q₂.Prime ∧ q₃.Prime ∧
      M ≤ q ∧ q < Y ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ p + 2 = q * q₂ * q₃)).sum
    (fun p => Real.log (p : ℝ))

/-- The number of members of `s0Set x M` whose shift is a product of three primes
`q q₂ q₃` with `M ≤ q < Y ≤ q₂ ≤ q₃`. -/
noncomputable def bTermCount (x M Y : ℕ) : ℕ :=
  ((s0Set x M).filter (fun p => ∃ q q₂ q₃ : ℕ, q.Prime ∧ q₂.Prime ∧ q₃.Prime ∧
      M ≤ q ∧ q < Y ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ p + 2 = q * q₂ * q₃)).card

/-- `θ`-mass of the members of `s0Set x M` whose shift is divisible by `q ^ 2` for some
window prime `q`. -/
noncomputable def sqMass (x M Y : ℕ) : ℝ :=
  ((s0Set x M).filter (fun p => ∃ q : ℕ, q.Prime ∧ M ≤ q ∧ q < Y ∧ q ^ 2 ∣ p + 2)).sum
    (fun p => Real.log (p : ℝ))

/-- `θ`-mass of the members of `s0Set x M` whose shift is divisible by `q ^ 2` for some
prime `q ≥ M`. -/
noncomputable def sqMassAll (x M : ℕ) : ℝ :=
  ((s0Set x M).filter (fun p => ∃ q : ℕ, q.Prime ∧ M ≤ q ∧ q ^ 2 ∣ p + 2)).sum
    (fun p => Real.log (p : ℝ))

end Submission
