import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.NumberTheory

/-- `1 + 2^n` is coprime to `2^(2n+1) - 1`.

Any common divisor `p` of `2^n + 1` and `2^(2n+1) - 1` also divides
`2^(2n) - 1 = (2^n + 1)(2^n - 1)`, hence divides
`(2^(2n+1) - 1) - 2(2^(2n) - 1) = 1`, so `p = 1`. -/
theorem coprime_one_add_two_pow_two_mul_succ_sub_one (n : ℕ) :
    Nat.Coprime (1 + 2 ^ n) (2 ^ (2 * n + 1) - 1) := by
  refine Nat.coprime_of_dvd' ?_
  intro p hp hpa hpb
  have hpa' : p ∣ 2 ^ n + 1 := by simpa [Nat.add_comm] using hpa
  -- 2^(2n) - 1 = (2^n + 1) * (2^n - 1)
  have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    have hpw : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
      rw [show 2 * n = n * 2 by omega, Nat.pow_mul]
    calc
      2 ^ (2 * n) - 1 = (2 ^ n) ^ 2 - 1 := by rw [hpw]
      _ = (2 ^ n) ^ 2 - (1 : ℕ) ^ 2 := by norm_num
      _ = (2 ^ n + 1) * (2 ^ n - 1) := Nat.sq_sub_sq (2 ^ n) 1
  have h1 : p ∣ 2 ^ (2 * n) - 1 := by
    rw [hfac]
    exact dvd_mul_of_dvd_left hpa' (2 ^ n - 1)
  have h2 : p ∣ 2 * (2 ^ (2 * n) - 1) := dvd_mul_of_dvd_right h1 2
  have hX : 2 * 2 ^ (2 * n) = 2 ^ (2 * n + 1) := by
    rw [show 2 * 2 ^ (2 * n) = 2 ^ (2 * n) * 2 by rw [mul_comm]]
    rw [← pow_succ]
  have hE : 2 * (2 ^ (2 * n) - 1) = 2 ^ (2 * n + 1) - 2 := by
    calc
      2 * (2 ^ (2 * n) - 1) = 2 * 2 ^ (2 * n) - 2 := by rw [Nat.mul_sub_one]
      _ = 2 ^ (2 * n + 1) - 2 := by rw [hX]
  have hge : 2 ≤ 2 ^ (2 * n + 1) := by
    have hpowpos : 1 ≤ 2 ^ (2 * n) := Nat.succ_le_of_lt (pow_pos (by norm_num) (2 * n))
    rw [← hX]
    nlinarith
  have hId : (2 ^ (2 * n + 1) - 1) - 2 * (2 ^ (2 * n) - 1) = 1 := by
    rw [hE]; omega
  have h3 : p ∣ (2 ^ (2 * n + 1) - 1) - 2 * (2 ^ (2 * n) - 1) := Nat.dvd_sub hpb h2
  simpa [hId] using h3

end Commons.NumberTheory
