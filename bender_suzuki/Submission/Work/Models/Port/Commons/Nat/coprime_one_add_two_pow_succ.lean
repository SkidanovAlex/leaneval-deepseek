import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.Nat

/-- `1 + 2^(n+1)` is coprime to `2^(2n+1) - 1`.

Idea: any common divisor `d` of `2^(n+1) + 1` and `2^(2n+1) - 1` also divides
`2^(2(n+1)) - 1 = (2^(n+1) + 1)(2^(n+1) - 1)`, hence divides the difference
`(2^(2(n+1)) - 1) - 2(2^(2n+1) - 1) = 1`, so `d = 1`.
-/
theorem coprime_one_add_two_pow_succ (n : ℕ) : Nat.Coprime (1 + 2 ^ (n + 1)) (2 ^ (2 * n + 1) - 1) := by
  refine Nat.coprime_of_dvd' ?_
  intro p hp hpa hpb
  have hpa' : p ∣ 2 ^ (n + 1) + 1 := by
    simpa [Nat.add_comm] using hpa
  -- 2^(2(n+1)) - 1 = (2^(n+1) + 1) * (2^(n+1) - 1)
  have hfac : 2 ^ (2 * (n + 1)) - 1 = (2 ^ (n + 1) + 1) * (2 ^ (n + 1) - 1) := by
    have hpw : 2 ^ (2 * (n + 1)) = (2 ^ (n + 1)) ^ 2 := by
      rw [show 2 * (n + 1) = (n + 1) * 2 by omega, Nat.pow_mul]
    calc
      2 ^ (2 * (n + 1)) - 1 = (2 ^ (n + 1)) ^ 2 - 1 := by rw [hpw]
      _ = (2 ^ (n + 1)) ^ 2 - (1 : ℕ) ^ 2 := by norm_num
      _ = (2 ^ (n + 1) + 1) * (2 ^ (n + 1) - 1) := by exact Nat.sq_sub_sq (2 ^ (n + 1)) 1
  -- hence p divides 2^(2(n+1)) - 1
  have h1 : p ∣ 2 ^ (2 * (n + 1)) - 1 := by
    rw [hfac]
    exact dvd_mul_of_dvd_left hpa' (2 ^ (n + 1) - 1)
  -- and p divides 2 * (2^(2n+1) - 1)
  have h2 : p ∣ 2 * (2 ^ (2 * n + 1) - 1) := dvd_mul_of_dvd_right hpb 2
  -- 2 * 2^(2n+1) = 2^(2(n+1))
  have hX : 2 * 2 ^ (2 * n + 1) = 2 ^ (2 * (n + 1)) := by
    have hExp : (2 * n + 1) + 1 = 2 * (n + 1) := by omega
    rw [mul_comm]
    rw [← pow_succ]
    rw [hExp]
  -- 2 * (2^(2n+1) - 1) = 2^(2(n+1)) - 2
  have hE : 2 * (2 ^ (2 * n + 1) - 1) = 2 ^ (2 * (n + 1)) - 2 := by
    calc
      2 * (2 ^ (2 * n + 1) - 1) = 2 * 2 ^ (2 * n + 1) - 2 := by rw [Nat.mul_sub_one]
      _ = 2 ^ (2 * (n + 1)) - 2 := by rw [← hX]
  have hge2 : 2 ≤ 2 ^ (2 * (n + 1)) := by
    have hpowpos : 1 ≤ 2 ^ (2 * n + 1) := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) (2 * n + 1))
    rw [← hX]
    nlinarith
  -- subtracting: (2^(2(n+1)) - 1) - 2 * (2^(2n+1) - 1) = 1
  have hId : (2 ^ (2 * (n + 1)) - 1) - 2 * (2 ^ (2 * n + 1) - 1) = 1 := by
    rw [hE]
    omega
  -- p divides the difference, i.e. p divides 1
  have h3 : p ∣ (2 ^ (2 * (n + 1)) - 1) - 2 * (2 ^ (2 * n + 1) - 1) := Nat.dvd_sub h1 h2
  simpa [hId] using h3

end Commons.Nat
