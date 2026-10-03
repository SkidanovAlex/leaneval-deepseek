import Mathlib
import Submission.Work.FIArea7.NCBasic

set_option linter.unusedVariables false

namespace Work.FIArea7

/-
# `Work.FIArea7.nc_core_arith`

Pure real-arithmetic assembly used by the numeric core of the Friedlander--Iwaniec proof.

Given the two "input" bounds
* `ha : (log (N+2))^23 * log N ≤ N^(3δ₁/8)`  and
* `hb : (log (N+2))^3 * (log N)^2 ≤ N^(1-δ₁/4)`

we bound the full expression produced by multiplying the constants `3000` and `2500` by the two
"head" logarithms and the two exponential factors.

Writing `M = log (N+2)`, `L = log N`, `P = N^(3δ₁/8)`, `Q = N^(1-δ₁/4)` the identity
`(N * N^(1-c)) * N^c = N^2` (valid for `N > 0`) turns the expression into
`7500000 * N^2 * L * (6 * (M^23 * L / P) + 2 * (M^3 * L^2 / Q))`, and the two hypotheses give
`M^23 * L ≤ P`, `M^3 * L^2 ≤ Q`.  Concretely the two summands are bounded by
`45000000 * N^2 * L` and `15000000 * N^2 * L`, whose sum is exactly the desired
`60000000 * N^2 * L`.
-/
theorem nc_core_arith {N δ₁ : ℝ} (hN5 : 5 ≤ N) (hδ0 : 0 < δ₁) (hδ32 : δ₁ < 3 / 32)
    (ha : (Real.log (N + 2)) ^ 23 * Real.log N ≤ N ^ (3 * δ₁ / 8))
    (hb : (Real.log (N + 2)) ^ 3 * (Real.log N) ^ 2 ≤ N ^ (1 - δ₁ / 4)) :
    3000 * N * (Real.log (N + 2)) ^ 3 * (2500 * (Real.log N) ^ 2)
      * (6 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 + 2 * N ^ (δ₁ / 4) * Real.log N)
      ≤ 60000000 * N ^ 2 * Real.log N := by
  have hN : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN1
  have hL0 : 0 ≤ Real.log N := le_of_lt hL
  -- `N * N^(1 - c) * N^c = N^2` for the two relevant exponents.
  have hid1 : N * N ^ (1 - 3 * δ₁ / 8) * N ^ (3 * δ₁ / 8) = N ^ 2 := by
    have h : N ^ (1 - 3 * δ₁ / 8) * N ^ (3 * δ₁ / 8) = N := by
      rw [← Real.rpow_add hN]
      have : (1 - 3 * δ₁ / 8) + (3 * δ₁ / 8) = (1 : ℝ) := by ring
      rw [this, Real.rpow_one]
    calc N * N ^ (1 - 3 * δ₁ / 8) * N ^ (3 * δ₁ / 8)
        = N * (N ^ (1 - 3 * δ₁ / 8) * N ^ (3 * δ₁ / 8)) := by ring
      _ = N * N := by rw [h]
      _ = N ^ 2 := by ring
  have hid2 : N * N ^ (δ₁ / 4) * N ^ (1 - δ₁ / 4) = N ^ 2 := by
    have h : N ^ (δ₁ / 4) * N ^ (1 - δ₁ / 4) = N := by
      rw [← Real.rpow_add hN]
      have : δ₁ / 4 + (1 - δ₁ / 4) = (1 : ℝ) := by ring
      rw [this, Real.rpow_one]
    calc N * N ^ (δ₁ / 4) * N ^ (1 - δ₁ / 4)
        = N * (N ^ (δ₁ / 4) * N ^ (1 - δ₁ / 4)) := by ring
      _ = N * N := by rw [h]
      _ = N ^ 2 := by ring
  -- First summand: `N * N^(1-3δ₁/8) * M^23 * L^2 ≤ N^2 * L`.
  have hA : N * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 23 * (Real.log N) ^ 2
      ≤ N ^ 2 * Real.log N := by
    have h1 : (Real.log (N + 2)) ^ 23 * (Real.log N) ^ 2
        ≤ N ^ (3 * δ₁ / 8) * Real.log N := by
      have hh := mul_le_mul_of_nonneg_right ha hL0
      nlinarith [hh]
    have h2 : N * N ^ (1 - 3 * δ₁ / 8) * ((Real.log (N + 2)) ^ 23 * (Real.log N) ^ 2)
        ≤ N * N ^ (1 - 3 * δ₁ / 8) * (N ^ (3 * δ₁ / 8) * Real.log N) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : N * N ^ (1 - 3 * δ₁ / 8) * (N ^ (3 * δ₁ / 8) * Real.log N)
        = N ^ 2 * Real.log N := by
      rw [show N * N ^ (1 - 3 * δ₁ / 8) * (N ^ (3 * δ₁ / 8) * Real.log N)
            = (N * N ^ (1 - 3 * δ₁ / 8) * N ^ (3 * δ₁ / 8)) * Real.log N by ring, hid1]
    nlinarith [h2, h3]
  -- Second summand: `N * N^(δ₁/4) * M^3 * L^3 ≤ N^2 * L`.
  have hB : N * N ^ (δ₁ / 4) * (Real.log (N + 2)) ^ 3 * (Real.log N) ^ 3
      ≤ N ^ 2 * Real.log N := by
    have h1 : (Real.log (N + 2)) ^ 3 * (Real.log N) ^ 3
        ≤ N ^ (1 - δ₁ / 4) * Real.log N := by
      have hh := mul_le_mul_of_nonneg_right hb hL0
      nlinarith [hh]
    have h2 : N * N ^ (δ₁ / 4) * ((Real.log (N + 2)) ^ 3 * (Real.log N) ^ 3)
        ≤ N * N ^ (δ₁ / 4) * (N ^ (1 - δ₁ / 4) * Real.log N) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : N * N ^ (δ₁ / 4) * (N ^ (1 - δ₁ / 4) * Real.log N)
        = N ^ 2 * Real.log N := by
      rw [show N * N ^ (δ₁ / 4) * (N ^ (1 - δ₁ / 4) * Real.log N)
            = (N * N ^ (δ₁ / 4) * N ^ (1 - δ₁ / 4)) * Real.log N by ring, hid2]
    nlinarith [h2, h3]
  -- Split the product into the two summands (a polynomial identity in the atoms).
  have hsplit : 3000 * N * (Real.log (N + 2)) ^ 3 * (2500 * (Real.log N) ^ 2)
      * (6 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 + 2 * N ^ (δ₁ / 4) * Real.log N)
      = 45000000 * (N * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 23 * (Real.log N) ^ 2)
        + 15000000 * (N * N ^ (δ₁ / 4) * (Real.log (N + 2)) ^ 3 * (Real.log N) ^ 3) := by
    ring
  have hA2 : 45000000 * (N * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 23 * (Real.log N) ^ 2)
      ≤ 45000000 * (N ^ 2 * Real.log N) :=
    mul_le_mul_of_nonneg_left hA (by norm_num)
  have hB2 : 15000000 * (N * N ^ (δ₁ / 4) * (Real.log (N + 2)) ^ 3 * (Real.log N) ^ 3)
      ≤ 15000000 * (N ^ 2 * Real.log N) :=
    mul_le_mul_of_nonneg_left hB (by norm_num)
  linarith [hsplit, hA2, hB2]

end Work.FIArea7
