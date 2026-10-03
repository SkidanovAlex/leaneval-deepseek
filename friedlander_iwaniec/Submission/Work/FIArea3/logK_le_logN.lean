import Mathlib

namespace Work.FIArea3

/-- **Logarithmic ceiling for the divisor-splitting parameters.** If `1 ≤ K`, `K ≤ 2·(c·θ·N)^{1/4}`
with `0 < c ≤ 16`, `0 < θ ≤ 1`, `1 ≤ N` and `log N ≥ 2^19`, then `log K + 2 ≤ log N`. -/
theorem logK_le_logN (N θ K c : ℝ) (hN : 1 ≤ N) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hc : 0 < c) (hc16 : c ≤ 16)
    (hlogN : (2 : ℝ) ^ (19 : ℕ) ≤ Real.log N)
    (hK : 1 ≤ K) (hKub : K ≤ 2 * (c * θ * N) ^ ((1 : ℝ) / 4)) :
    Real.log K + 2 ≤ Real.log N := by
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hctNpos : 0 < c * θ * N := mul_pos (mul_pos hc hθ) hNpos
  have hcθ_le : c * θ ≤ 16 := by nlinarith [hc.le, hθ, hθ1, hc16]
  have h1 : c * θ * N ≤ 16 * N := by
    have := mul_le_mul_of_nonneg_right hcθ_le hNpos.le
    linarith [this]
  have h16Npos : 0 < 16 * N := by linarith [hNpos]
  have h2 : (c * θ * N) ^ ((1 : ℝ) / 4) ≤ (16 * N) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hctNpos.le h1 (by norm_num)
  have hKub' : K ≤ 2 * (16 * N) ^ ((1 : ℝ) / 4) := by
    have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 by norm_num)
    linarith [hKub, this]
  have hlogK : Real.log K ≤ Real.log (2 * (16 * N) ^ ((1 : ℝ) / 4)) :=
    Real.log_le_log hKpos hKub'
  have hlog16N : Real.log (16 * N) = Real.log 16 + Real.log N :=
    Real.log_mul (by norm_num) hNpos.ne'
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    have h : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have hval : Real.log (2 * (16 * N) ^ ((1 : ℝ) / 4)) = 2 * Real.log 2 + (1 / 4) * Real.log N := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow h16Npos, hlog16N, hlog16]
    ring
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogNbig : (4 : ℝ) ≤ (3 / 4) * Real.log N := by
    have h2p : (2 : ℝ) ^ (19 : ℕ) = 524288 := by norm_num
    rw [h2p] at hlogN
    nlinarith [hlogN]
  linarith [hlogK, hval, hlog2le, hlogNbig]

end Work.FIArea3
