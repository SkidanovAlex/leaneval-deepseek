import Mathlib
import Submission.ChenPlan.Interfaces

/-!
# The linear sieve for `BoundingSieve`: basic vocabulary

Definitions used by the Jurkat–Richert development of the linear sieve
(`Work.ChenPlan.LinearSieve.linear_sieve`).

* `siftedSumLt s z` : the mass of the support elements that are not divisible by any prime of
  `P = s.prodPrimes` which is `< z` (the sifted sum with sift limit `z`).  For `z` larger than
  every prime of `P` this is Mathlib's `BoundingSieve.siftedSum`.
* `smallestPFMass s p` : the mass of the elements whose smallest prime divisor coming from `P`
  is exactly `p` (the "Buchstab cell" of `p`).
* `gSum s ξ` : Selberg's `G(ξ,z) = Σ_{d ∣ P, d < ξ} h(d)`, `h(p) = ν(p)/(1-ν(p))`
  (Mathlib's `BoundingSieve.selbergTerms` is exactly `h`).
* `remTrunc s D` : the truncated remainder sum `Σ_{d ∣ P, d < D} 3^{ω(d)} |r_d|`
  (definitionally `Submission.ChenPlan.remSum s D`).
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve

/-- Sifted sum with sift limit `z`: the weight of the support elements that are not divisible by
any prime of `P` that is `< z`. -/
noncomputable def siftedSumLt (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ n ∈ s.support,
    if ∀ p ∈ s.prodPrimes.primeFactors, p < z → ¬ p ∣ n then s.weights n else 0

/-- The Buchstab cell of `p`: the weight of the elements whose smallest prime divisor from `P`
is exactly `p`. -/
noncomputable def smallestPFMass (s : BoundingSieve) (p : ℕ) : ℝ :=
  ∑ n ∈ s.support,
    if p ∣ n ∧ ∀ q ∈ s.prodPrimes.primeFactors, q < p → ¬ q ∣ n then s.weights n else 0

/-- Selberg's `G(ξ,z) = Σ_{d ∣ P, d < ξ} h(d)`, with `h(d) = ∏_{p ∣ d} ν(p)/(1-ν(p))`
(Mathlib's `BoundingSieve.selbergTerms`). -/
noncomputable def gSum (s : BoundingSieve) (ξ : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < ξ),
    (s.selbergTerms) d

/-- The truncated remainder sum: definitionally `Submission.ChenPlan.remSum s D`. -/
noncomputable def remTrunc (s : BoundingSieve) (D : ℝ) : ℝ :=
  Submission.ChenPlan.remSum s D

/-- The middle divisor range used by the Selberg sieve with weight level `ξ`: the divisisors of
`P` below `ξ²` (where the `λ²` sieve keeps its error terms). -/
noncomputable def remSelberg (s : BoundingSieve) (ξ : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < ξ ^ 2),
    (3 : ℝ) ^ d.primeFactors.card * |s.rem d|

end Work.ChenPlan.LinearSieve

namespace Work.ChenPlan.LinearSieve

/-- The Selberg sieve error sum `Σ_{d ∣ P} |λ²(w)(d)| |r_d|`. -/
noncomputable def lambdaErrSum (s : BoundingSieve) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors,
    |BoundingSieve.lambdaSquared w d| * |s.rem d|

/-- The Möbius remainder sum `Σ_{d ∣ P} μ(d) r_d`. -/
noncomputable def moebiusRemSum (s : BoundingSieve) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * s.rem d

/-- The Buchstab cell sum `Σ_{w ≤ p < z, p ∣ P} (weight of the elements whose smallest prime
divisor from `P` is `p`)`. -/
noncomputable def cellSum (s : BoundingSieve) (w z : ℕ) : ℝ :=
  ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ p ∧ p < z),
    smallestPFMass s p

/-- The full (untruncated) Selberg sum `Σ_{d ∣ P} h(d)`. -/
noncomputable def selbergTermsSum (s : BoundingSieve) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, (s.selbergTerms) d

end Work.ChenPlan.LinearSieve
