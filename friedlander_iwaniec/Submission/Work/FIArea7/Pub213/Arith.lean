/-
# `Work.FIArea7.Pub213.Arith` — the arithmetic of the `k = 6` Hölder step (*FI* (21.9))

The two ingredients of the exponent bookkeeping: the identity that converts the shape produced by
the `k = 6` Hölder step into the target shape of (21.9), and the logarithm comparison
`log(M N⁶ + 2) ≤ 7 log(M N + 2)` (the mean square is used at radius `N⁶`).
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea7.Pub213

noncomputable section

lemma rpow_mul_same {x : ℝ} (hx : 0 < x) (a b : ℝ) : x ^ a * x ^ b = x ^ (a + b) :=
  (Real.rpow_add hx a b).symm

/-- The Hölder shape `M^{5/6}N^{1/2}(N^{1/2}M^{1/12} + N^{1/4}M^{1/3} + M^{1/2})` is exactly the
target shape `M^{11/12}N + M^{7/6}N^{3/4} + M^{4/3}N^{1/2}` of (21.9). -/
lemma holder6_arith {M N c A : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    c * (M ^ ((5 : ℝ) / 6) * N ^ ((1 : ℝ) / 2)
        * (N ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 12) + N ^ ((1 : ℝ) / 4) * M ^ ((1 : ℝ) / 3)
            + M ^ ((1 : ℝ) / 2))
        * (Real.log (M * N + 2)) ^ A)
      = c * (M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
            + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2))
          * (Real.log (M * N + 2)) ^ A := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have e1 : M ^ ((5 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * (N ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 12))
      = M ^ ((11 : ℝ) / 12) * N := by
    have h1 : M ^ ((5 : ℝ) / 6) * M ^ ((1 : ℝ) / 12) = M ^ ((11 : ℝ) / 12) := by
      rw [rpow_mul_same hM0, show (5 : ℝ) / 6 + (1 : ℝ) / 12 = (11 : ℝ) / 12 by norm_num]
    have h2 : N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) = N := by
      rw [rpow_mul_same hN0, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
    calc M ^ ((5 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * (N ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 12))
        = (M ^ ((5 : ℝ) / 6) * M ^ ((1 : ℝ) / 12)) * (N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2)) := by
          ring
      _ = M ^ ((11 : ℝ) / 12) * N := by rw [h1, h2]
  have e2 : M ^ ((5 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * (N ^ ((1 : ℝ) / 4) * M ^ ((1 : ℝ) / 3))
      = M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4) := by
    have h1 : M ^ ((5 : ℝ) / 6) * M ^ ((1 : ℝ) / 3) = M ^ ((7 : ℝ) / 6) := by
      rw [rpow_mul_same hM0, show (5 : ℝ) / 6 + (1 : ℝ) / 3 = (7 : ℝ) / 6 by norm_num]
    have h2 : N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 4) = N ^ ((3 : ℝ) / 4) := by
      rw [rpow_mul_same hN0, show (1 : ℝ) / 2 + (1 : ℝ) / 4 = (3 : ℝ) / 4 by norm_num]
    calc M ^ ((5 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * (N ^ ((1 : ℝ) / 4) * M ^ ((1 : ℝ) / 3))
        = (M ^ ((5 : ℝ) / 6) * M ^ ((1 : ℝ) / 3)) * (N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 4)) := by
          ring
      _ = M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4) := by rw [h1, h2]
  have e3 : M ^ ((5 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2)
      = M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) := by
    have h1 : M ^ ((5 : ℝ) / 6) * M ^ ((1 : ℝ) / 2) = M ^ ((4 : ℝ) / 3) := by
      rw [rpow_mul_same hM0, show (5 : ℝ) / 6 + (1 : ℝ) / 2 = (4 : ℝ) / 3 by norm_num]
    calc M ^ ((5 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2)
        = (M ^ ((5 : ℝ) / 6) * M ^ ((1 : ℝ) / 2)) * N ^ ((1 : ℝ) / 2) := by ring
      _ = M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) := by rw [h1]
  have hmain : M ^ ((5 : ℝ) / 6) * N ^ ((1 : ℝ) / 2)
        * (N ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 12) + N ^ ((1 : ℝ) / 4) * M ^ ((1 : ℝ) / 3)
            + M ^ ((1 : ℝ) / 2))
      = M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
          + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) := by
    rw [mul_add, mul_add, e1, e2, e3]
  rw [hmain]
  ring

/-- `log(M N⁶ + 2) ≤ 7 log(M N + 2)`: the mean square is consumed at radius `N⁶`. -/
lemma log_MN6_le {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    Real.log (M * N ^ 6 + 2) ≤ 7 * Real.log (M * N + 2) := by
  have hMN : (1 : ℝ) ≤ M * N := by nlinarith
  have h6 : M * N ^ 6 ≤ (M * N) ^ 6 := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h := pow_le_pow_right₀ hM (by norm_num : 1 ≤ 6)
    simpa using h
  have h5 : M * N ^ 6 + 2 ≤ 3 * (M * N + 2) ^ 6 := by
    have h7 : (M * N) ^ 6 ≤ (M * N + 2) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
    have h8 : (1 : ℝ) ≤ (M * N + 2) ^ 6 := by
      have h9 : (1 : ℝ) ≤ M * N + 2 := by linarith
      calc (1 : ℝ) = 1 ^ 6 := by norm_num
        _ ≤ (M * N + 2) ^ 6 := pow_le_pow_left₀ (by norm_num) h9 6
    linarith
  have h1 : (0 : ℝ) < M * N ^ 6 + 2 := by positivity
  have h2 : Real.log (M * N ^ 6 + 2) ≤ Real.log (3 * (M * N + 2) ^ 6) :=
    Real.log_le_log h1 h5
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
  have h2' : Real.log (M * N ^ 6 + 2) ≤ Real.log 3 + 6 * Real.log (M * N + 2) := by
    simpa using h2
  have h3 : Real.log 3 ≤ Real.log (M * N + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  linarith

/-- `log(N + 2) ≤ log(M N + 2)`. -/
lemma log_N_le {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    Real.log (N + 2) ≤ Real.log (M * N + 2) :=
  Real.log_le_log (by linarith) (by nlinarith)

/-- `1 ≤ log(M N + 2)` for `M, N ≥ 1`. -/
lemma one_le_log_MN {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    (1 : ℝ) ≤ Real.log (M * N + 2) := by
  have h1 : (3 : ℝ) ≤ M * N + 2 := by nlinarith
  have h2 : Real.log 3 ≤ Real.log (M * N + 2) := Real.log_le_log (by norm_num) h1
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three.le
  linarith

end

end Work.FIArea7.Pub213
