import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem stirling_sq_identity (x : ℝ) (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    (Real.sqrt (2 * Real.pi * x) * (x / Real.exp 1) ^ n) ^ 2 =
      x ^ 2 * (2 * Real.pi * x ^ (2 * n - 1) * Real.exp (-(2 * (n : ℝ)))) := by
  have hA : (Real.sqrt (2 * Real.pi * x)) ^ 2 = 2 * Real.pi * x := Real.sq_sqrt (by positivity)
  have hB : ((x / Real.exp 1) ^ n) ^ 2 = x ^ (2 * n) * Real.exp (-(2 * (n : ℝ))) := by
    rw [div_pow, div_pow, ← pow_mul x n 2, ← pow_mul (Real.exp 1) n 2]
    rw [show n * 2 = 2 * n from by omega]
    rw [← Real.exp_nat_mul 1 (2 * n)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_one]
    rw [Real.exp_neg, div_eq_mul_inv]
  rw [mul_pow, hA, hB]
  have hl : x * x ^ (2 * n) = x ^ (2 * n + 1) := by rw [mul_comm, ← pow_succ]
  have hp : x ^ 2 * x ^ (2 * n - 1) = x ^ (2 * n + 1) := by
    rw [← pow_add]; congr 1; omega
  have hPQ : x * x ^ (2 * n) = x ^ 2 * x ^ (2 * n - 1) := by rw [hl, hp]
  have h1 : 2 * Real.pi * x * (x ^ (2 * n) * Real.exp (-(2 * (n : ℝ))))
      = 2 * Real.pi * (x * x ^ (2 * n)) * Real.exp (-(2 * (n : ℝ))) := by ring
  have h2 : x ^ 2 * (2 * Real.pi * x ^ (2 * n - 1) * Real.exp (-(2 * (n : ℝ))))
      = 2 * Real.pi * (x ^ 2 * x ^ (2 * n - 1)) * Real.exp (-(2 * (n : ℝ))) := by ring
  rw [h1, h2, hPQ]

end Work.BW
