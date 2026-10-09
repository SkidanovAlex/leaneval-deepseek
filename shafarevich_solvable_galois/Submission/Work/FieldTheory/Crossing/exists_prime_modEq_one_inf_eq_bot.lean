import Mathlib
import Submission.Work.FieldTheory.Crossing.Defs
import Submission.Work.FieldTheory.Crossing.Disjoint
import Submission.Work.FieldTheory.Crossing.FiniteBadPrimes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FieldTheory.Crossing

open scoped Nat

set_option linter.style.haveILetI false

/-- Escape from the finite set of "bad" primes `p` with `CycloField p ⊓ L ≠ ⊥`.

For a finite-dimensional Galois `L : IntermediateField ℚ (AlgebraicClosure ℚ)`, every `n ≠ 0`
and every lower bound `B`, there is a prime `p > B` with `p ≡ 1 [MOD n]` and
`CycloField p ⊓ L = ⊥`.

Proof: the bad primes form a finite set (`finite_bad_primes`), bound it by `B₀`, and apply
Dirichlet's theorem `Nat.exists_prime_gt_modEq_one` with lower bound `max B B₀`. -/
theorem exists_prime_modEq_one_inf_eq_bot (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hfd : FiniteDimensional ℚ L) (hG : IsGalois ℚ L) (n B : ℕ) (hn : n ≠ 0) :
    ∃ p, Nat.Prime p ∧ B < p ∧ p ≡ 1 [MOD n] ∧ CycloField p ⊓ L = ⊥ := by
  obtain ⟨B₀, hB₀⟩ := (finite_bad_primes L hfd hG).bddAbove
  obtain ⟨p, hp, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (max B B₀) hn
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left B B₀) hgt, hmod, ?_⟩
  by_contra hne
  have hmem : p ∈ ({p : ℕ | Nat.Prime p ∧ CycloField p ⊓ L ≠ ⊥} : Set ℕ) := ⟨hp, hne⟩
  have := hB₀ hmem
  omega

end Work.FieldTheory.Crossing
