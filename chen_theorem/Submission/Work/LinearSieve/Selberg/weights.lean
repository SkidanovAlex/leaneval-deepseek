import Mathlib
import Submission.Work.ChenPlan.LinearSieve.basic

/-!
# Selberg's optimal `Λ²` weights

For a `BoundingSieve` `s` and a level `ξ > 1`, the optimal Selberg weights are
`w d = μ(d) T_d / (G(ξ) ν(d))` for the divisors `d` of `P = s.prodPrimes` with `d < ξ`, and `0`
otherwise; here `G(ξ) = Σ_{l ∣ P, l < ξ} h(l)` (`Work.ChenPlan.LinearSieve.gSum`) and
`T_d = Σ_{l ∣ P, d ∣ l, l < ξ} h(l)`.  These are the weights that minimise the main term of the
`Λ²` sieve, with minimum value `1/G(ξ)`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.LinearSieve.Selberg

/-- The tail `T_d = Σ_{l ∣ P, d ∣ l, l < ξ} h(l)` of Selberg's `G`-sum over the multiples of `d`. -/
noncomputable def tailG (s : BoundingSieve) (ξ : ℝ) (d : ℕ) : ℝ :=
  ∑ l ∈ s.prodPrimes.divisors.filter (fun l => d ∣ l ∧ (l : ℝ) < ξ), (s.selbergTerms) l

/-- Selberg's optimal `Λ²` weights for level `ξ`. -/
noncomputable def selbergWeight (s : BoundingSieve) (ξ : ℝ) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes ∧ (d : ℝ) < ξ then
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * tailG s ξ d
      / (Work.ChenPlan.LinearSieve.gSum s ξ * s.nu d)
  else 0

end Work.LinearSieve.Selberg
