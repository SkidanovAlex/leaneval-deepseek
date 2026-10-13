import Mathlib

namespace Work.DSM4p

universe a
/-- In a commutative ring `R` of characteristic a prime `p`, if the Frobenius map
`x ↦ x ^ p` is bijective (i.e. `R` is perfect), then `R` is reduced.

The key step is that if `x ^ p = 0` then `(1 + x) ^ p = 1 + x ^ p = 1 = 1 ^ p`, so by
injectivity of the Frobenius map `1 + x = 1`, whence `x = 0`. A nilpotent element `x`
with `x ^ n = 0` then satisfies `x ^ (p ^ n) = 0`, and iterating the previous observation
(using `x ^ p ^ (k + 1) = (x ^ p ^ k) ^ p`) gives `x = 0`. -/
theorem isReduced_perfectRing {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] : IsReduced R := by
  -- An element whose `p`-th power vanishes is zero.
  have key : ∀ x : R, x ^ p = 0 → x = 0 := by
    intro x hx
    have h : (1 + x) ^ p = 1 ^ p := by
      rw [add_pow_char, one_pow, hx, add_zero]
    have h' : (1 : R) + x = 1 := injective_pow_p R p h
    have h'' : (1 : R) + x = 1 + 0 := by rw [add_zero]; exact h'
    exact add_left_cancel h''
  -- Iterating, an element whose `p ^ k`-th power vanishes is zero.
  have keyPow : ∀ k : ℕ, ∀ x : R, x ^ p ^ k = 0 → x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      exact ih x (key (x ^ p ^ k) (by rw [← pow_mul, ← pow_succ p k]; exact hx))
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hnle : n ≤ p ^ n := le_trans (le_of_lt n.lt_two_pow_self) (pow_le_pow_left' hp2 n)
  exact keyPow n x (pow_eq_zero_of_le hnle hn)

end Work.DSM4p
