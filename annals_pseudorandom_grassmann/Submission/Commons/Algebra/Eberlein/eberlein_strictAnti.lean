import Mathlib

namespace Commons.Algebra.Eberlein

theorem eberlein_strictAnti (m n i : ℕ) (him : i + 1 ≤ m) (hin : i + 1 ≤ n) :
    (2 ^ (i + 2) * (2 ^ (m - (i + 1)) - 1) * (2 ^ (n - (i + 1)) - 1) : ℤ) - (2 ^ (i + 1) - 1) <
      (2 ^ (i + 1) * (2 ^ (m - i) - 1) * (2 ^ (n - i) - 1) : ℤ) - (2 ^ i - 1) := by
  -- Exponents: `m - i = (m - (i + 1)) + 1` and same for `n`.
  have hm : m - i = (m - (i + 1)) + 1 := by omega
  have hn : n - i = (n - (i + 1)) + 1 := by omega
  -- Rewrite all powers in terms of the atoms `2 ^ i`, `2 ^ (m - (i+1))`, `2 ^ (n - (i+1))`.
  have hi2 : (2 : ℤ) ^ (i + 2) = 4 * 2 ^ i := by rw [pow_add (2 : ℤ) i 2]; ring
  have hi1 : (2 : ℤ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_add (2 : ℤ) i 1]; ring
  have hpm : (2 : ℤ) ^ (m - i) = 2 * 2 ^ (m - (i + 1)) := by
    rw [hm, pow_add (2 : ℤ) (m - (i + 1)) 1]; ring
  have hpn : (2 : ℤ) ^ (n - i) = 2 * 2 ^ (n - (i + 1)) := by
    rw [hn, pow_add (2 : ℤ) (n - (i + 1)) 1]; ring
  rw [hi2, hi1, hpm, hpn]
  -- Abbreviate the three positive atoms.
  set A : ℤ := 2 ^ i with hA
  set P : ℤ := 2 ^ (m - (i + 1)) with hP
  set Q : ℤ := 2 ^ (n - (i + 1)) with hQ
  have hA1 : (1 : ℤ) ≤ A := by rw [hA]; exact one_le_pow₀ (by norm_num)
  have hP1 : (1 : ℤ) ≤ P := by rw [hP]; exact one_le_pow₀ (by norm_num)
  have hQ1 : (1 : ℤ) ≤ Q := by rw [hQ]; exact one_le_pow₀ (by norm_num)
  -- The difference of the two sides equals `A * (4 * P * Q - 1)`, which is positive.
  have key : (2 * A * (2 * P - 1) * (2 * Q - 1)) - (A - 1)
      - ((4 * A * (P - 1) * (Q - 1)) - (2 * A - 1)) = A * (4 * P * Q - 1) := by ring
  have hApos : 0 < A := by linarith
  have hPQ : 0 < 4 * P * Q - 1 := by nlinarith [hP1, hQ1]
  have hpos : 0 < A * (4 * P * Q - 1) := mul_pos hApos hPQ
  linarith [key, hpos]

end Commons.Algebra.Eberlein
