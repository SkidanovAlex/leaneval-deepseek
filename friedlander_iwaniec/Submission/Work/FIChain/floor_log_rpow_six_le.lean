import Mathlib

namespace Work.FIChain

/-- Floor-comparison for the logarithmic weight: for `u ≥ 2`, with `n = ⌊u⌋₊ ≥ 2` one has
`u < n + 1 ≤ n²`, hence `u < ⌊u⌋₊²` and `log u < 2·log ⌊u⌋₊`; since `t ↦ t^{-6}` is antitone
on the positives this gives `(log ⌊u⌋₊)^{-6} ≤ 64·(log u)^{-6}`.  (Note: the naive route
`⌊u⌋₊ > u/2 ⟹ log ⌊u⌋₊ ≥ (1/2)log u` needs a case split and is not the clean path; the
bound `u < ⌊u⌋₊²` is uniform in `u ≥ 2`.) -/
theorem floor_log_rpow_six_le (u : ℝ) (hu : 2 ≤ u) :
    (Real.log (⌊u⌋₊ : ℝ)) ^ (-6 : ℝ) ≤ 64 * (Real.log u) ^ (-6 : ℝ) := by
  set n : ℕ := ⌊u⌋₊ with hn
  -- `n = ⌊u⌋₊ ≥ 2`
  have hn2 : 2 ≤ n := by rw [hn]; exact Nat.le_floor hu
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hu1 : (1 : ℝ) < u := by linarith
  have hn1 : (1 : ℝ) < (n : ℝ) := by linarith
  -- `u < n + 1 ≤ n²`
  have hu_lt : u < (n : ℝ) ^ 2 := by
    have h1 : u < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one u
    have h2 : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith
    linarith
  have hlogu_pos : 0 < Real.log u := Real.log_pos hu1
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  -- `log u < log (n²) = 2 log n`
  have hlt : Real.log u < 2 * Real.log (n : ℝ) := by
    have h := Real.log_lt_log (by linarith : (0 : ℝ) < u) hu_lt
    rw [Real.log_pow] at h
    simpa using h
  -- antitone decay of `t ↦ t^{-6}` on the positives
  have hmain : (2 * Real.log (n : ℝ)) ^ (-6 : ℝ) ≤ (Real.log u) ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hlogu_pos (le_of_lt hlt) (by norm_num)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hlogn_pos)] at hmain
  have h2 : (2 : ℝ) ^ (-6 : ℝ) = 64⁻¹ := by
    rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    norm_num
  rw [h2] at hmain
  nlinarith [hmain]

end Work.FIChain
