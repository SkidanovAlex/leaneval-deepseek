import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.local_prime_sqrtWeight

/-!
# The prime-modulus (`e = 1`) local correlation bound

`local_prime_sqrtWeight` (unit U9 of `BURGESS_ROUTE_LEAD.md`) bounds the correlation of two
triples of linear factors modulo a prime `p`, for a *non-trivial* character of level `p`.
The assembly `singleton_sum_all` consumes that bound at the primes `p` of `q` with exponent
`e = 1`, i.e. for a character `χ : DirichletCharacter ℂ (p ^ 1)` of level `p ^ 1 = p` which is
assumed *primitive* rather than explicitly non-trivial.

Since `p ^ 1 = p` the two statements are the same statement, only the level is written as a
power; and since `p` is prime, a primitive character of level `p` cannot be the trivial
character (the trivial character has conductor `1 ≠ p`).  This file performs that reduction:
it transports the general-level statement along `p ^ 1 = p` and applies
`local_prime_sqrtWeight`, deriving `χ ≠ 1` from `χ.IsPrimitive`.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

/-- The `e = 1` local correlation bound for an arbitrary level `N` which is (propositionally)
equal to the prime `p`.  Substituting `N := p` reduces it verbatim to
`local_prime_sqrtWeight`, the only extra input being `χ ≠ 1`, which follows from primitivity
because the trivial character has conductor `1` while `conductor χ = N = p ≥ 2`. -/
private lemma local_corr_level_prime {p : ℕ} [Fact p.Prime] (N : ℕ) [NeZero N] (hN : N = p)
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (i : Fin 6) :
    ‖∑ x : ZMod N, χ (∏ l : Fin 3, (x + (a l : ZMod N)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod N))))‖
      ≤ 6 * Real.sqrt (p : ℝ) * sqrtGcdW p i (shift a b) := by
  subst N
  have hne : χ ≠ 1 := by
    intro h
    have hc := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mp h
    rw [DirichletCharacter.isPrimitive_def] at hχ
    rw [hχ] at hc
    exact (Fact.out : Nat.Prime p).ne_one hc
  exact local_prime_sqrtWeight χ hne a b i

/-- **U9 at exponent `1`.**  The square-root weighted bound for the correlation of two products of
three linear factors modulo `p = p ^ 1`, for a primitive character of level `p ^ 1`. -/
theorem local_prime_powOne_bound {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ (p ^ 1))
    (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (i : Fin 6) :
    ‖∑ x : ZMod (p ^ 1), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ 1))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ 1)))))‖
      ≤ 6 * Real.sqrt (p : ℝ) * sqrtGcdW p i (shift a b) :=
  local_corr_level_prime (p ^ 1) (pow_one p) χ hχ a b i

end Work.LinnikBurgess
