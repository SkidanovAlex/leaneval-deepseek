import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux

/-- The `c ≥ 1/16` branch of the Rauch comparison constant.  Written out: with `c ∈ [1/16, 1/4]`,
`4 ε₁ π < c` and `ε₁ ≥ 0`, one has

`6 (ε₁ (1 + (log (4 / √c))²) + c/4) + (c/4) log (8/c) ≤ 7 c`.

The proof only uses the elementary bounds `√c ≥ 1/4 ⟺ c ≥ 1/16`, hence
`log (4/√c) ≤ 4 log 2`, `log (8/c) ≤ 7 log 2`, together with `π ∈ (3.1415, 3.1416)` and
`log 2 < 0.69315`. -/
theorem rauch_B_large {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) (h16 : 1 / 16 ≤ c) :
    6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4) + (c / 4) * Real.log (8 / c) ≤ 7 * c := by
  have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  -- `log c ≥ -log 16`
  have hlogc : Real.log (1 / 16 : ℝ) ≤ Real.log c := Real.log_le_log (by norm_num) h16
  have hlogc' : -Real.log (16 : ℝ) ≤ Real.log c := by
    rwa [Real.log_div one_ne_zero (by norm_num : (16 : ℝ) ≠ 0), Real.log_one, zero_sub] at hlogc
  -- powers of two
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [h, Real.log_pow]; ring
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have h : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [h, Real.log_pow]; ring
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h, Real.log_pow]; ring
  -- `log (4/√c) ≤ 4 log 2`
  have hL4 : Real.log (4 / Real.sqrt c) ≤ 4 * Real.log 2 := by
    have hlogd : Real.log (4 / Real.sqrt c) = Real.log 4 - Real.log (Real.sqrt c) :=
      Real.log_div (by norm_num) (ne_of_gt hsqrt_pos)
    have hlogs : Real.log (Real.sqrt c) = Real.log c / 2 := Real.log_sqrt (le_of_lt hc)
    rw [hlogd, hlogs, hlog4]
    nlinarith [hlogc', hlog16]
  -- `0 ≤ log (4/√c)`
  have hL0 : 0 ≤ Real.log (4 / Real.sqrt c) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hsqrt_pos]
    nlinarith [Real.sqrt_nonneg c, Real.sq_sqrt (le_of_lt hc), hc1]
  -- hence `1 + (log (4/√c))² ≤ 1 + 16 (log 2)²`
  have hB : 1 + (Real.log (4 / Real.sqrt c)) ^ 2 ≤ 1 + 16 * (Real.log 2) ^ 2 := by
    have h := mul_self_le_mul_self hL0 hL4
    nlinarith [h]
  -- `log (8/c) ≤ 7 log 2`
  have hM7 : Real.log (8 / c) ≤ 7 * Real.log 2 := by
    have hlogd : Real.log (8 / c) = Real.log 8 - Real.log c :=
      Real.log_div (by norm_num) (ne_of_gt hc)
    rw [hlogd, hlog8]
    nlinarith [hlogc', hlog16]
  have h4pi : 0 < 4 * Real.pi := by positivity
  -- the numerical kernel `6(1+16 log²2) + 6π + 7π log 2 ≤ 28π`
  have hnum : 6 * (1 + 16 * (Real.log 2) ^ 2) + 6 * Real.pi + 7 * Real.pi * Real.log 2 ≤ 28 * Real.pi := by
    have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hl : Real.log 2 ≤ 0.69315 := by linarith [Real.log_two_lt_d9]
    have hp1 : (3.1415 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d4
    have hp2 : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
    nlinarith [mul_self_le_mul_self hl0 hl]
  have hnumc : c * (6 * (1 + 16 * (Real.log 2) ^ 2) + 6 * Real.pi + 7 * Real.pi * Real.log 2)
      ≤ c * (28 * Real.pi) :=
    mul_le_mul_of_nonneg_left hnum (le_of_lt hc)
  -- multiply the goal through by `4π > 0`
  suffices hkey : 4 * Real.pi *
      (6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4) + (c / 4) * Real.log (8 / c))
      ≤ 4 * Real.pi * (7 * c) by
    exact le_of_mul_le_mul_left hkey h4pi
  have hA1 : 24 * Real.pi * ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2)
      ≤ 6 * c * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) := by
    have hpos : 0 < 6 * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) := by
      have h2 : 0 ≤ (Real.log (4 / Real.sqrt c)) ^ 2 := sq_nonneg _
      linarith
    have hstep := mul_lt_mul_of_pos_right hnum2 hpos
    nlinarith [hstep]
  have hA2 : 6 * c * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) ≤ 6 * c * (1 + 16 * (Real.log 2) ^ 2) :=
    mul_le_mul_of_nonneg_left hB (by linarith)
  have hC : Real.pi * c * Real.log (8 / c) ≤ Real.pi * c * (7 * Real.log 2) :=
    mul_le_mul_of_nonneg_left hM7 (by positivity)
  have hs : 6 * c * (1 + 16 * (Real.log 2) ^ 2) + 6 * Real.pi * c
      + Real.pi * c * (7 * Real.log 2) ≤ 28 * Real.pi * c := by
    nlinarith [hnumc]
  have hexp : 4 * Real.pi *
        (6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4) + (c / 4) * Real.log (8 / c))
      = 24 * Real.pi * ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2)
        + 6 * Real.pi * c + Real.pi * c * Real.log (8 / c) := by
    ring
  have hR : 4 * Real.pi * (7 * c) = 28 * Real.pi * c := by ring
  rw [hexp, hR]
  linarith [hA1, hA2, hC, hs]

end Work.Diff.C.geoCrux
