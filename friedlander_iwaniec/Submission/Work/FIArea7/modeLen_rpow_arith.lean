import Mathlib
import Submission.Work.FIArea7.Bridge17Defs
import Submission.Work.FIArea7.modeLen_bounds

namespace Work.FIArea7

/-- The composition's exponent `nuU = 3·sigmaChoice Asave + 4` equals `3012582943`. -/
lemma nuU_le_num : Work.FITop4.nuU ≤ 3012582943 := by
  unfold Work.FITop4.nuU Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
  norm_num

/-- **Real-power arithmetic for the §17 mode length**: in the regime `1 ≤ s ≤ 4L`, `L ≥ 8192`
and `β = 100524288 = 2²⁰/… ` the product `8192 · s^β · L^{ν}` with `ν = nuU·3/2` is swallowed
by `L^{5·10⁹}`.  The exponents add up to `2β + ν + 7 ≤ 4719922997.5 ≤ 5·10⁹`. -/
theorem modeLen_rpow_arith {s L : ℝ} (hs1 : 1 ≤ s) (hL4 : 4 ≤ L) (hL8 : 8192 ≤ L) (hsl : s ≤ 4 * L) :
    8192 * (s ^ (100524288 : ℝ) * L ^ (Work.FITop4.nuU * (3 / 2))) * L ^ (6 : ℝ) ≤ L ^ (5 * 10 ^ 9 : ℝ) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hnu0 : (0 : ℝ) ≤ Work.FITop4.nuU * (3 / 2) := by
    have h : (0 : ℝ) ≤ Work.FITop4.nuU := by
      unfold Work.FITop4.nuU Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
      norm_num
    linarith
  have hcore := rpow_polylog_core (C := (8192 : ℝ)) (s := s) (t := L)
    (β := (100524288 : ℝ)) (ν := Work.FITop4.nuU * (3 / 2))
    (by norm_num) hL8 hs1 hL4 hsl (by norm_num) hnu0
  have hLHS : 8192 * (s ^ (100524288 : ℝ) * L ^ (Work.FITop4.nuU * (3 / 2))) * L ^ (6 : ℝ)
      = 8192 * s ^ (100524288 : ℝ) * L ^ (Work.FITop4.nuU * (3 / 2) + 6) := by
    rw [Real.rpow_add hL0]
    ring
  rw [hLHS]
  refine le_trans hcore ?_
  apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ L)
  have h1 : 2 * (100524288 : ℝ) + Work.FITop4.nuU * (3 / 2) + 7 ≤ 4719922997.5 := by
    linarith [nuU_le_num]
  linarith

end Work.FIArea7
