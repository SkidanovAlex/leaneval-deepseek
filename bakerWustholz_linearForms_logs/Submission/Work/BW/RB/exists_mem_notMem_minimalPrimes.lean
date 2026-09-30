import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.RB

/-- Given a prime ideal `p` whose height strictly exceeds the height of every minimal
prime over `I`, there is an element of `p` lying in none of those minimal primes.

Proof: if every element of `p` lay in some minimal prime of `I`, then `p` would be
covered by the (finitely many, by Noetherianity) minimal primes of `I`, all of which
are prime. Prime avoidance then forces `p` to be contained in one minimal prime `Q`,
whence `p.height ≤ Q.height < p.height`, a contradiction. -/
theorem exists_mem_notMem_minimalPrimes {R : Type*} [CommRing R] [IsNoetherianRing R]
    {I p : Ideal R} [p.IsPrime]
    (h : ∀ Q ∈ I.minimalPrimes, Q.height < p.height) :
    ∃ x ∈ p, ∀ Q ∈ I.minimalPrimes, x ∉ Q := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ x ∈ p, ∃ Q ∈ I.minimalPrimes, x ∈ Q`, so `p` is covered by the minimal primes.
  have hsub : (p : Set R) ⊆ ⋃ Q ∈ I.minimalPrimes, (Q : Set R) := by
    intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := hcon x hx
    exact Set.mem_biUnion hQ hxQ
  -- Prime avoidance: `p` is contained in one of the (prime) minimal primes.
  obtain ⟨Q, hQ, hpQ⟩ := (Ideal.subset_union_prime_finite
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R I) (⊥ : Ideal R) (⊥ : Ideal R)
    (fun i hi _ _ => Ideal.IsMinimalPrime.isPrime hi)).mp hsub
  -- Monotonicity of height contradicts `Q.height < p.height`.
  exact absurd (lt_of_le_of_lt (Ideal.height_mono hpQ) (h Q hQ)) (lt_irrefl p.height)

end Work.BW.RB
