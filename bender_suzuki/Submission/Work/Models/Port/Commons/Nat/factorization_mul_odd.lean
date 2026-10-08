import Mathlib.Data.Nat.Factorization.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.Nat

theorem factorization_mul_odd (a b : ℕ) (hb : Odd b) :
    (a * b).factorization 2 = a.factorization 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hb0 : b ≠ 0 := fun h => hb.not_two_dvd_nat (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul ha hb0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (p := 2) hb.not_two_dvd_nat, add_zero]

end Commons.Nat