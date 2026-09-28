import Mathlib
import Submission.Work.HP.MDEstimates.ceil_logb_cube_le
import Submission.Work.HP.MDEstimates.ceil_logb_rpow_le

/-!
# `q44_log_bound`

For `Kmink ≥ 1` there is `K > 0` with
`(⌈logb 2 (8 Kmink (Δ+1))⌉₊ + 1)^3 * 2^(71 ⌈logb 2 (8 Kmink (Δ+1))⌉₊ / 3) ≤ K Δ^24`
for every real `Δ ≥ 1`.

Write `x = 8 Kmink (Δ+1)` and `n = ⌈logb 2 x⌉₊`.  The two factors are estimated separately,
using the two arithmetic inputs proved in `MDEstimates`:

* `ceil_logb_cube_le : (n+1)^3 ≤ (9/log 2 + 2)^3 · x^(1/3)` (the polylogarithmic factor is
  `O(Δ^{1/3})`);
* `ceil_logb_rpow_le : 2^(71n/3) ≤ 2^(71/3) · x^(71/3)` (the exponential factor equals
  `x^{71/3}` up to the fixed factor `2^{71/3}`).

Since `x^(1/3) · x^(71/3) = x^24` and `x ≤ 2 · (8 Kmink) · 2 · Δ` (as `Δ + 1 ≤ 2Δ`), the
product is `≤ K Δ^24`.
-/

namespace Work.HP.Q44Main

theorem q44_log_bound (Kmink : ℝ) (hKmink : 1 ≤ Kmink) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 3
        * (2 : ℝ) ^ (71 * (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) / 3)
      ≤ K * Δ ^ 24 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKm : 0 < Kmink := lt_of_lt_of_le zero_lt_one hKmink
  refine ⟨(9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) * (8 * Kmink) ^ 24 * 2 ^ 24,
    ?_, ?_⟩
  · have h1 : (0 : ℝ) < 9 / Real.log 2 + 2 := by positivity
    positivity
  · intro Δ hΔ
    set x : ℝ := 8 * Kmink * (Δ + 1) with hxdef
    set n : ℕ := ⌈Real.logb 2 x⌉₊ with hndef
    have hx1 : 1 ≤ x := by rw [hxdef]; nlinarith [hKmink, hΔ]
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    -- polylogarithmic factor
    have hn1 : ((n : ℝ) + 1) ^ 3 ≤ (9 / Real.log 2 + 2) ^ 3 * x ^ ((1 : ℝ) / 3) :=
      Work.HP.MDEstimates.ceil_logb_cube_le x hx1
    -- exponential factor
    have hn2 : (2 : ℝ) ^ (71 * (n : ℝ) / 3) ≤ (2 : ℝ) ^ ((71 : ℝ) / 3) * x ^ ((71 : ℝ) / 3) :=
      Work.HP.MDEstimates.ceil_logb_rpow_le x hx1
    -- combine the two `x`-powers
    have hxpow : x ^ ((1 : ℝ) / 3) * x ^ ((71 : ℝ) / 3) = x ^ 24 := by
      rw [← Real.rpow_add hxpos]
      norm_num
    -- `x^24 ≤ (8 Kmink)^24 · 2^24 · Δ^24`
    have hx24 : x ^ 24 ≤ (8 * Kmink) ^ 24 * 2 ^ 24 * Δ ^ 24 := by
      rw [hxdef]
      have hstep : (Δ + 1) ^ 24 ≤ 2 ^ 24 * Δ ^ 24 := by
        have h : (Δ + 1) ^ 24 ≤ (2 * Δ) ^ 24 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 24
        rwa [mul_pow] at h
      calc (8 * Kmink * (Δ + 1)) ^ 24
          = (8 * Kmink) ^ 24 * (Δ + 1) ^ 24 := by rw [mul_pow]
        _ ≤ (8 * Kmink) ^ 24 * (2 ^ 24 * Δ ^ 24) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = (8 * Kmink) ^ 24 * 2 ^ 24 * Δ ^ 24 := by ring
    -- the two estimates multiply
    have hcomb : ((n : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (71 * (n : ℝ) / 3)
        ≤ (9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) * x ^ 24 := by
      calc ((n : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (71 * (n : ℝ) / 3)
          ≤ ((9 / Real.log 2 + 2) ^ 3 * x ^ ((1 : ℝ) / 3))
              * ((2 : ℝ) ^ ((71 : ℝ) / 3) * x ^ ((71 : ℝ) / 3)) :=
            mul_le_mul hn1 hn2 (by positivity) (by positivity)
        _ = (9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3)
              * (x ^ ((1 : ℝ) / 3) * x ^ ((71 : ℝ) / 3)) := by ring
        _ = (9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) * x ^ 24 := by rw [hxpow]
    have hfinal : (9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) * x ^ 24
        ≤ ((9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) * (8 * Kmink) ^ 24 * 2 ^ 24)
            * Δ ^ 24 := by
      have hnn : (0 : ℝ) ≤ (9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) := by
        have h1 : (0 : ℝ) < 9 / Real.log 2 + 2 := by positivity
        positivity
      calc (9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) * x ^ 24
          = ((9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3)) * x ^ 24 := by ring
        _ ≤ ((9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3))
              * ((8 * Kmink) ^ 24 * 2 ^ 24 * Δ ^ 24) :=
              mul_le_mul_of_nonneg_left hx24 hnn
        _ = ((9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) * (8 * Kmink) ^ 24 * 2 ^ 24)
              * Δ ^ 24 := by ring
    calc ((n : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (71 * (n : ℝ) / 3)
        ≤ (9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) * x ^ 24 := hcomb
      _ ≤ ((9 / Real.log 2 + 2) ^ 3 * (2 : ℝ) ^ ((71 : ℝ) / 3) * (8 * Kmink) ^ 24 * 2 ^ 24)
            * Δ ^ 24 := hfinal

end Work.HP.Q44Main
