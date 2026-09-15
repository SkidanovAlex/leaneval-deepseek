import Mathlib

namespace Commons.Data.Nat

theorem eq_sum_digits {p l x : ℕ} (hp : 1 ≤ p) (hx : x < p ^ l) :
    x = ∑ j ∈ Finset.range l, (x / p ^ j % p) * p ^ j := by
  have hp0 : 0 < p := hp
  induction l generalizing x with
  | zero =>
    rw [pow_zero] at hx
    simp only [Finset.sum_range_zero]
    omega
  | succ l ih =>
    have hx' : x / p < p ^ l := by
      rw [Nat.div_lt_iff_lt_mul hp0, ← pow_succ]
      exact hx
    have ihx := ih hx'
    have hterm : ∀ j, (x / p ^ (j + 1) % p) * p ^ (j + 1)
        = p * ((x / p / p ^ j % p) * p ^ j) := by
      intro j
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      ring
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.div_one, mul_one]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, ← ihx,
      Nat.div_add_mod]

end Commons.Data.Nat
