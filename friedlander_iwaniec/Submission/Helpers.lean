import Mathlib

namespace Submission.Helpers

/-- End-game glue for the Friedlander–Iwaniec theorem: a subset of `ℕ` is
infinite iff it contains elements arbitrarily far out, so it suffices to
produce, for every `N`, a prime `p > N` of the form `a² + b⁴`.  The deep
analytic work (asymptotic sieve for primes) is what supplies the existence;
this lemma only bridges from "unbounded" to "infinite". -/
theorem infinite_X2Y4_primes_of_unbounded
    (h : ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4) :
    {p : ℕ | p.Prime ∧ ∃ a b, p = a ^ 2 + b ^ 4}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  rcases h N with ⟨p, hgt, hp⟩
  exact ⟨p, hp, hgt⟩

end Submission.Helpers
