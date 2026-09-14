import Mathlib.Data.Nat.Factorial.BigOperators

set_option autoImplicit false

namespace Commons.Data.Nat

theorem factorial_mul_lt (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a.factorial * b.factorial < (a + b).factorial := by
  -- Identity: (a + b)! = a! * ∏ i ∈ range b, (a + i + 1)
  have hprod : (a + b).factorial =
      a.factorial * ∏ i ∈ Finset.range b, (a + i + 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    rw [Finset.prod_range_add]
    rw [Finset.prod_range_add_one_eq_factorial]
  -- b! = ∏ i ∈ range b, (i + 1) < ∏ i ∈ range b, (a + i + 1), since a ≥ 1
  have hb_lt : b.factorial < ∏ i ∈ Finset.range b, (a + i + 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    exact Finset.prod_lt_prod_of_nonempty
      (f := fun i : ℕ => i + 1) (g := fun i : ℕ => a + i + 1)
      (s := Finset.range b)
      (by intro i hi; omega)
      (by intro i hi; omega)
      (by rw [Finset.nonempty_range_iff]; omega)
  rw [hprod]
  exact (Nat.mul_lt_mul_left (Nat.factorial_pos a)).2 hb_lt

end Commons.Data.Nat