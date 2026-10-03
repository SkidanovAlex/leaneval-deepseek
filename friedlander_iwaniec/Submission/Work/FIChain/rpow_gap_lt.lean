import Mathlib
import Submission.Work.FITop.RCPrelude

namespace Work.FIChain

/-- For `0 < η < 1/32`, the function `x ↦ x ^ (5/16 - 3η/32)/2` eventually dominates
`x ↦ x ^ (1/4 + η/4) + 1`: the difference of exponents is `1/16 - 11η/32 > 0`. -/
theorem rpow_gap_lt (η : ℝ) (hη : 0 < η) (hη16 : η < 1 / 32) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η / 4) + 1 < (x : ℝ) ^ ((5 : ℝ) / 16 - 3 * η / 32) / 2 := by
  set a : ℝ := 1 / 4 + η / 4 with ha
  set b : ℝ := 5 / 16 - 3 * η / 32 with hb
  -- the exponents differ by `1/16 - 11η/32 > 0`
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hd : 0 < b - a := by
    have h : 11 * η / 32 < 11 / 1024 := by linarith [hη16]
    rw [ha, hb]; linarith
  -- `x ↦ x^(b-a)` tends to `+∞`, hence is eventually at least `4`
  have htend : Filter.Tendsto (fun x : ℕ => (x : ℝ) ^ (b - a)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (4 : ℝ), Filter.eventually_ge_atTop 2] with x hx4 hx2
  have hx2' : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  -- `x^a > 2^a > 1`
  have hxa_gt1 : 1 < (x : ℝ) ^ a :=
    lt_of_lt_of_le (Real.one_lt_rpow (by norm_num) ha_pos)
      (Real.rpow_le_rpow (by norm_num) hx2' (le_of_lt ha_pos))
  have hxa_nn : 0 ≤ (x : ℝ) ^ a := Real.rpow_nonneg (le_of_lt hxpos) a
  -- split `x^b = x^a * x^(b-a)`
  have hsplit : (x : ℝ) ^ b = (x : ℝ) ^ a * (x : ℝ) ^ (b - a) := by
    conv_lhs => rw [show b = a + (b - a) by ring]
    exact Real.rpow_add hxpos a (b - a)
  have hmul : (x : ℝ) ^ a * 4 ≤ (x : ℝ) ^ a * (x : ℝ) ^ (b - a) :=
    mul_le_mul_of_nonneg_left hx4 hxa_nn
  rw [hsplit]
  linarith

end Work.FIChain
