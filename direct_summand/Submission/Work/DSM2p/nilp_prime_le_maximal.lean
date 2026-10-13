import Mathlib

/-!
# Computing via a fractional ideal: a prime below a maximal ideal avoiding a nonzerodivisor

If `x` is a nonzerodivisor in a commutative ring `R` and `M` is a maximal ideal of `R`, then `M`
contains a prime ideal `P` with `x ∉ P`: take `P` minimal among the primes contained in `M`; the
elements of a minimal prime are zero divisors, so a nonzerodivisor avoids it.
-/

namespace Work.DSM2p

/-- A maximal ideal contains a prime ideal avoiding a given nonzerodivisor. -/
theorem nilp_prime_le_maximal {R : Type*} [CommRing R] (M : Ideal R) [M.IsMaximal]
    {x : R} (hx : x ∈ M) (hreg : IsSMulRegular R x) :
    ∃ P : Ideal R, P.IsPrime ∧ P ≤ M ∧ x ∉ P := by
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := M) bot_le
  refine ⟨p, hp.1.1, hple, ?_⟩
  have hann : (Module.annihilator R R : Ideal R) = ⊥ := by
    ext r
    rw [Ideal.mem_bot]
    constructor
    · intro h
      have := (Module.mem_annihilator (R := R)).1 (show r ∈ Module.annihilator R R from h) 1
      simpa using this
    · intro h
      subst h
      rw [Module.mem_annihilator]
      intro m
      simp
  rw [← hann] at hp
  exact IsSMulRegular.notMem_of_mem_minimalPrimes hreg hp

end Work.DSM2p
