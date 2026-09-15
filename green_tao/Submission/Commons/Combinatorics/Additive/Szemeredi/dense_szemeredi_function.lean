import Mathlib
import Submission.Commons.Combinatorics.Additive.Szemeredi.finite_szemeredi
import Submission.Commons.Combinatorics.Additive.Szemeredi.prime_engine_of_finite_szemeredi
import Submission.Commons.Combinatorics.Additive.Szemeredi.many_aps_of_prime_engine_function

namespace Commons.Combinatorics.Additive.Szemeredi

/-- Quantitative dense Szemerédi/Varnavides statement in the cyclic group `ZMod p`
for primes `p`: a `[0,1]`-valued weight `g` of total mass at least `δ * p` has at
least `c * p^2` weighted `k`-term arithmetic progressions.

Assembled from the shared commons: `finite_szemeredi` (the finitary Szemerédi
theorem, obtained via density Hales–Jewett) feeds
`prime_engine_of_finite_szemeredi` (a single dense block contains a nontrivial AP),
which feeds `many_aps_of_prime_engine_function` (averaging over windows produces
the quadratic count of weighted APs). -/
theorem dense_szemeredi_function {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : ∃ c : ℝ, 0 < c ∧ ∃ P₀ : ℕ, ∀ (p : ℕ) [NeZero p], Nat.Prime p → P₀ ≤ p → ∀ g : ZMod p → ℝ, (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → δ * (p : ℝ) ≤ ∑ x, g x → c * (p : ℝ) ^ 2 ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ j ∈ Finset.range k, g (x + (j : ZMod p) * r) :=
  many_aps_of_prime_engine_function
    (prime_engine_of_finite_szemeredi (fun k δ hδ => finite_szemeredi k δ hδ))
    k hk δ hδ

end Commons.Combinatorics.Additive.Szemeredi
