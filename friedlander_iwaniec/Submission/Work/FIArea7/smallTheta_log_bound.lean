import Mathlib
import Submission.Work.FITop.Defs

namespace Work.FIArea7

/-- Logarithmic comparison of `Work.FIArea7.area7_small_theta`: with `θ ≤ 1` the kernel
logarithm `log(8(1+θ)N)` is at most `4 log(N+2)` (since `8(1+θ)N ≤ 16N`, `log 16 ≤ 3` and
`log(N+2) ≥ 1` for `N ≥ 1`). -/
theorem smallTheta_log_bound {Pa : Work.FITop.Params} (hθ1 : Pa.θ ≤ 1) :
    Real.log (8 * (1 + Pa.θ) * Pa.N) ≤ 4 * Real.log (Pa.N + 2) := by
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  -- `8(1+θ)N ≤ 16N`, and `log(16N) = log 16 + log N`.
  have harg1pos : 0 < 8 * (1 + Pa.θ) * Pa.N := by nlinarith [hθ0, hN1]
  have hle : 8 * (1 + Pa.θ) * Pa.N ≤ 16 * Pa.N := by nlinarith [hθ1, hN1]
  have hlog1 : Real.log (8 * (1 + Pa.θ) * Pa.N) ≤ Real.log (16 * Pa.N) :=
    Real.log_le_log harg1pos hle
  have hmul : Real.log (16 * Pa.N) = Real.log 16 + Real.log Pa.N :=
    Real.log_mul (by norm_num) (by linarith)
  -- `log 16 ≤ log((N+2)^3) = 3 log(N+2)` since `16 ≤ 27 ≤ (N+2)^3` for `N ≥ 1`.
  have h16 : Real.log 16 ≤ 3 * Real.log (Pa.N + 2) := by
    have h3 : (3:ℝ) ≤ Pa.N + 2 := by linarith [hN1]
    have hp : (16:ℝ) ≤ (Pa.N + 2)^3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) h3 3
      norm_num at h; linarith
    have h1 : Real.log 16 ≤ Real.log ((Pa.N + 2)^3) :=
      Real.log_le_log (by norm_num) hp
    have h2 : Real.log ((Pa.N + 2)^3) = 3 * Real.log (Pa.N + 2) := by
      rw [Real.log_pow]; norm_num
    linarith [h1, h2.le, h2.ge]
  -- `log N ≤ log(N+2)`.
  have hNle : Real.log Pa.N ≤ Real.log (Pa.N + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith [hlog1, hmul.le, hmul.ge, h16, hNle]

end Work.FIArea7
