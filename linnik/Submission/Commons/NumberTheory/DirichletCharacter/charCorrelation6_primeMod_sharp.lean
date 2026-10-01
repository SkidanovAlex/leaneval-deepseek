import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_cubefree_global

namespace Commons.NumberTheory.DirichletCharacter

/-- **Sharp cubic correlation bound at a prime modulus (unique-value case).**

For a prime `p`, a non-trivial `χ` mod `p`, and shifts `a b : Fin 3 → ℕ` whose six values
`v = ![](a0,a1,a2,b0,b1,b2)` have `v i` occurring exactly once,
`‖∑_{x : ZMod p} χ ((x+a0)(x+a1)(x+a2)) conj (χ ((x+b0)(x+b1)(x+b2)))‖`
`≤ 6 √p · ∏_{j ≠ i} gcd p |v_i - v_j|`.

This is the `e = 1` analogue (with the gcd weight) of the proven
`Commons.NumberTheory.DirichletCharacter.charCorrelation6_cubefree_global`; it is the input for
the `v_p(q) = 1` case of the CRT product over the prime factors.

Proof route: if the pair is "good" in the sense of
`Commons.NumberTheory.DirichletCharacter.charCorrelation6_primeMod_good` (the multiplicity
functions of the two triples of shifts are not congruent modulo `orderOf χ` at some `x`), that
result gives `≤ 6 √p ≤ 6 √p ∏_{j ≠ i} gcd p |v_i - v_j|`, since all gcd factors are `≥ 1`.
Otherwise (`bad`) the trivial bound gives `≤ p`; and `bad` implies that some *other* shift is
congruent to `v i` modulo `p`: the value `v i` has multiplicity `1` in one of the two triples
and `0` in the other, which can never be congruent modulo `orderOf χ ≥ 2`, so unless another
shift is `≡ v i (mod p)` the pair is good.  Hence `p ∣ gcd p |v_i - v_j|` for some `j ≠ i`, so
`∏_{j ≠ i} gcd p |v_i - v_j| ≥ p` and
`p ≤ 6 √p · p ≤ 6 √p · ∏_{j ≠ i} gcd p |v_i - v_j|`. -/
theorem charCorrelation6_primeMod_sharp {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → (![a 0, a 1, a 2, b 0, b 1, b 2] i)
        ≠ (![a 0, a 1, a 2, b 0, b 1, b 2] j)) :
    ‖∑ x : ZMod p, χ (∏ l : Fin 3, (x + (a l : ZMod p))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod p))))‖
      ≤ 6 * Real.sqrt (p : ℝ) * ∏ j ∈ Finset.univ.erase i,
            (((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
               - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
  -- The prime-modulus bound is the `v_p(q) = 1` case of the cube-free global theorem; since `p`
  -- is prime its prime-factor set is a singleton, and `6 ^ 1 = 6`.
  have hp : p.Prime := Fact.out
  have hcard : p.primeFactors.card = 1 := by
    rw [hp.primeFactors]
    simp
  have h := charCorrelation6_prime_global (p := p) χ hχ a b i
  rw [hcard, pow_one] at h
  exact h

end Commons.NumberTheory.DirichletCharacter
