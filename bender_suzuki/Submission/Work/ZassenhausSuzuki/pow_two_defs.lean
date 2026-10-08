import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The odd part of a natural number

`oddPart n` is `n` with all factors of `2` removed, i.e. `n / 2 ^ (n.factorization 2)`
(Mathlib's `Nat.ordCompl[2] n`).  This little module collects the elementary API that the
arithmetic lemmas for `Work.ZassenhausSuzuki.pow_two_classification` use.

The point of restating everything in terms of `oddPart` is that the Mathlib notation
`Nat.ordCompl[2] n` is only available after `open Nat`, which makes it awkward to use in a
standalone statement; `oddPart` is definitionally the same thing.
-/

namespace Work.ZassenhausSuzuki

/-- The odd part of `n`: `n` with all factors of `2` removed. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ n.factorization 2

lemma oddPart_mul (a b : ℕ) : oddPart (a * b) = oddPart a * oddPart b :=
  Nat.ordCompl_mul a b 2

lemma oddPart_dvd (n : ℕ) : oddPart n ∣ n := Nat.ordCompl_dvd n 2

lemma oddPart_le (n : ℕ) : oddPart n ≤ n := Nat.ordCompl_le n 2

lemma oddPart_pos {n : ℕ} (hn : n ≠ 0) : 0 < oddPart n := Nat.ordCompl_pos 2 hn

lemma not_two_dvd_oddPart {n : ℕ} (hn : n ≠ 0) : ¬ 2 ∣ oddPart n :=
  Nat.not_dvd_ordCompl Nat.prime_two hn

lemma oddPart_self_pow_mul (m k : ℕ) : oddPart (2 ^ k * m) = oddPart m :=
  Nat.ordCompl_self_pow_mul m k Nat.prime_two

lemma oddPart_eq_self_of_odd {n : ℕ} (hn : Odd n) : oddPart n = n := by
  rw [oddPart]
  exact (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n Nat.prime_two).mpr
    (Or.inr (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hn))

/-- If the odd part of `N` is `1` then `N` is a power of two. -/
lemma exists_pow_two_of_oddPart_eq_one {N : ℕ} (h : oddPart N = 1) : ∃ j, N = 2 ^ j := by
  refine ⟨N.factorization 2, ?_⟩
  have h2 := Nat.ordProj_mul_ordCompl_eq_self N 2
  simp only [oddPart] at h
  rw [h, mul_one] at h2
  exact h2.symm

end Work.ZassenhausSuzuki
