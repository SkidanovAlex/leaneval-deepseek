import Mathlib.Algebra.GroupWithZero.Nat

namespace Commons.Data.Nat

theorem mul_div_gcd_eq_lcm (q r : ℕ) : q * (r / Nat.gcd q r) = Nat.lcm q r := by
  by_cases hg : Nat.gcd q r = 0
  · rcases (Nat.gcd_eq_zero_iff.mp hg) with ⟨rfl, rfl⟩
    simp
  · have hgpos : 0 < Nat.gcd q r := Nat.pos_of_ne_zero hg
    have hmul :
        q * (r / Nat.gcd q r) * Nat.gcd q r = Nat.lcm q r * Nat.gcd q r := by
      calc
        q * (r / Nat.gcd q r) * Nat.gcd q r =
            q * ((r / Nat.gcd q r) * Nat.gcd q r) := by
          rw [Nat.mul_assoc]
        _ = q * r := by
          rw [Nat.div_mul_cancel (Nat.gcd_dvd_right q r)]
        _ = Nat.lcm q r * Nat.gcd q r := by
          rw [Nat.lcm_mul_gcd]
    exact Nat.mul_right_cancel hgpos hmul

end Commons.Data.Nat