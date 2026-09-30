import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option linter.unusedVariables false

namespace Work.Pi6.EMZ

/-- A finite abelian group in which multiplication by `2`, and by every odd prime `p`,
is surjective is trivial.  (Finiteness + divisibility by `Nat.card G` forces every
element to be `0`; the torsion hypothesis `htor` is then not needed.)

The divisibility hypotheses only concern primes, but they combine: writing `n = p * m`
with `p` a prime and using strong induction on `n` shows multiplication by *every*
positive `n` is surjective. -/
theorem finiteTrivial (G : Type) [AddCommGroup G] [Finite G]
    (h2 : ∀ x : G, ∃ y : G, 2 • y = x)
    (hdiv : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : G, ∃ y : G, p • y = x)
    (htor : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : G, p • x = 0 → x = 0) :
    Subsingleton G := by
  -- Multiplication by every positive natural number is surjective.
  have hdiv' : ∀ n : ℕ, 0 < n → ∀ x : G, ∃ y : G, n • y = x := by
    intro n
    refine Nat.strong_induction_on n (fun n ih => ?_)
    intro hn x
    by_cases h1 : n = 1
    · subst h1
      exact ⟨x, one_nsmul x⟩
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨m, hm⟩ := hpdvd
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hm
          rw [hm] at hn
          exact absurd hn (lt_irrefl 0)
        · exact h
      have hmlt : m < n := by
        rw [hm]
        have h1' : m < 2 * m := by omega
        have h2' : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp.two_le
        omega
      obtain ⟨z, hz⟩ := ih m hmlt hmpos x
      -- `z` is `m`-divisible; divide it by the prime `p`.
      obtain ⟨y, hy⟩ : ∃ y : G, p • y = z := by
        by_cases hp2 : p = 2
        · rw [hp2]; exact h2 z
        · exact hdiv p hp hp2 z
      exact ⟨y, by rw [hm, mul_nsmul y p m, hy, hz]⟩
  have hzero : ∀ x : G, x = 0 := by
    intro x
    have hpos : 0 < Nat.card G := Nat.card_pos_iff.2 ⟨⟨0⟩, inferInstance⟩
    obtain ⟨y, hy⟩ := hdiv' (Nat.card G) hpos x
    have hy0 : Nat.card G • y = 0 := card_nsmul_eq_zero' (G := G) (x := y)
    rw [hy0] at hy
    exact hy.symm
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

end Work.Pi6.EMZ
