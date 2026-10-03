import Mathlib
import Submission.Work.FIArea7.NCBasic

namespace Work.FIArea7

/-- Elementary bound: `θ N + √N + 1 ≤ 3N` for `N ≥ 3`, `θ ≤ 1`. -/
lemma nc_A_linear {N θ : ℝ} (hN3 : 3 ≤ N) (hθ1 : θ ≤ 1) :
    θ * N + Real.sqrt N + 1 ≤ 3 * N := by
  have hN0 : 0 ≤ N := by linarith
  have h1 : (1 : ℝ) ≤ N := by linarith
  have hθN : θ * N ≤ N := by
    have h := mul_le_mul_of_nonneg_right hθ1 hN0
    simpa using h
  have hsqrt : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  linarith

theorem nc_A_bound {N θ : ℝ} (hN3 : 3 ≤ N) (hθ1 : θ ≤ 1) :
    1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3
      ≤ 3000 * N * (Real.log (N + 2)) ^ 3 := by
  have hL : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith)
  have hL3 : 0 ≤ (Real.log (N + 2)) ^ 3 := pow_nonneg hL 3
  have hA : θ * N + Real.sqrt N + 1 ≤ 3 * N := nc_A_linear hN3 hθ1
  have hb : 1000 * (θ * N + Real.sqrt N + 1) ≤ 3000 * N := by linarith
  rw [show (2 : ℝ) + N = N + 2 by ring]
  calc 1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3
      = (1000 * (θ * N + Real.sqrt N + 1)) * (Real.log (N + 2)) ^ 3 := by ring
    _ ≤ (3000 * N) * (Real.log (N + 2)) ^ 3 := mul_le_mul_of_nonneg_right hb hL3
    _ = 3000 * N * (Real.log (N + 2)) ^ 3 := by ring

end Work.FIArea7
