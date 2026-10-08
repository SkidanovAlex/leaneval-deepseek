import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- Closed form for the quotient when the exponent is odd, over `ℤ`:
`(x+1) * (1 + (x-1) * ∑_{j<k} x^{2j+1}) = x^{2k+1} + 1`. -/
private lemma geom_odd_int (x : ℤ) (k : ℕ) :
    (x + 1) * (1 + (x - 1) * (∑ j ∈ Finset.range k, x ^ (2 * j + 1))) =
      x ^ (2 * k + 1) + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rw [show 1 + (x - 1) * ((∑ j ∈ Finset.range k, x ^ (2 * j + 1)) + x ^ (2 * k + 1))
          = (1 + (x - 1) * (∑ j ∈ Finset.range k, x ^ (2 * j + 1)))
              + (x - 1) * x ^ (2 * k + 1) by ring]
    rw [mul_add, ih]
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
    ring

/-- The same closed form over `ℕ`. -/
private lemma geom_odd_nat (r k : ℕ) (hr : 1 ≤ r) :
    (r + 1) * (1 + (r - 1) * (∑ j ∈ Finset.range k, r ^ (2 * j + 1))) =
      r ^ (2 * k + 1) + 1 := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hr]
  exact geom_odd_int (r : ℤ) k

/-- The quotient is odd: `1` plus an even number. -/
private lemma parity (r k : ℕ) (hr : Odd r) :
    Odd (1 + (r - 1) * (∑ j ∈ Finset.range k, r ^ (2 * j + 1))) := by
  have heven : Even (r - 1) := by
    obtain ⟨m, hm⟩ := hr
    exact ⟨m, by omega⟩
  exact odd_one.add_even (heven.mul_right _)

theorem cofactor_odd (r n : ℕ) (hr : Odd r) (hn : Odd n) : Odd ((r ^ n + 1) / (r + 1)) := by
  obtain ⟨m, rfl⟩ := hn
  have hr1 : 1 ≤ r := by obtain ⟨s, hs⟩ := hr; omega
  have hA := geom_odd_nat r m hr1
  have hodd := parity r m hr
  have hdiv : (1 + (r - 1) * (∑ j ∈ Finset.range m, r ^ (2 * j + 1)))
      = (r ^ (2 * m + 1) + 1) / (r + 1) :=
    Nat.eq_div_of_mul_eq_right (Nat.succ_ne_zero r) hA
  rw [← hdiv]
  exact hodd

end Work.NormalComplement
