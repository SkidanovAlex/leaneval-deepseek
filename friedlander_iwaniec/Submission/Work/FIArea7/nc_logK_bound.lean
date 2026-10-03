import Mathlib
import Submission.Work.FIArea7.NCBasic

namespace Work.FIArea7

/-- Two-step logarithm bound: for `N ≥ 5` and `1 ≤ X` with `X^8 ≤ N^δ₁` and `δ₁ < 3/32`,
`3 log X ≤ log N`. -/
lemma three_mul_log_le {N X δ₁ : ℝ} (hN5 : 5 ≤ N) (hX1 : 1 ≤ X)
    (hX8 : X ^ 8 ≤ N ^ δ₁) (hδ32 : δ₁ < 3 / 32) :
    3 * Real.log X ≤ Real.log N := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hX0 : 0 < X := by linarith
  have hX8pos : 0 < X ^ 8 := by positivity
  have hlogX : 8 * Real.log X ≤ δ₁ * Real.log N := by
    have h := Real.log_le_log hX8pos hX8
    rwa [Real.log_pow, Real.log_rpow hN0] at h
  have h1 : 3 * Real.log X ≤ (3 * δ₁ / 8) * Real.log N := by nlinarith [hlogX]
  have h2 : (3 * δ₁ / 8) * Real.log N ≤ 1 * Real.log N := by
    apply mul_le_mul_of_nonneg_right _ hlogN0
    linarith [hδ32]
  linarith

/-- `20 log log (N+2) ≤ 40 log N` for `N ≥ 5`. -/
lemma twenty_log_log_le {N : ℝ} (hN5 : 5 ≤ N) :
    20 * Real.log (Real.log (N + 2)) ≤ 40 * Real.log N := by
  have hN1 : 1 ≤ N := by linarith
  have hL1 : 1 ≤ Real.log (N + 2) := one_le_log_of_three_le (by linarith)
  have hLpos : 0 < Real.log (N + 2) := by linarith
  have hLle : Real.log (N + 2) ≤ 2 * N := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < N + 2 by linarith)
    linarith
  have hlogL : Real.log (Real.log (N + 2)) ≤ Real.log (2 * N) := Real.log_le_log hLpos hLle
  have hmul : Real.log (2 * N) = Real.log 2 + Real.log N := Real.log_mul (by norm_num) (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by linarith)
  linarith

theorem nc_logK_bound {N X δ₁ : ℝ} {K : ℕ}
    (hN5 : 5 ≤ N) (hX1 : 1 ≤ X) (hX8 : X ^ 8 ≤ N ^ δ₁) (hδ0 : 0 < δ₁) (hδ32 : δ₁ < 3 / 32)
    (hK1 : 1 ≤ (K : ℝ)) (hKhi : (K : ℝ) ≤ 2 * X ^ 3 * (Real.log (N + 2)) ^ 20) :
    (Real.log ((K : ℝ) + 2)) ^ 2 ≤ 2500 * (Real.log N) ^ 2 := by
  have hN1 : 1 ≤ N := by linarith
  have hN4 : 4 ≤ N := by linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have h3X : 3 * Real.log X ≤ Real.log N := three_mul_log_le hN5 hX1 hX8 hδ32
  have h20L : 20 * Real.log (Real.log (N + 2)) ≤ 40 * Real.log N := twenty_log_log_le hN5
  have hL1 : 1 ≤ Real.log (N + 2) := one_le_log_of_three_le (by linarith)
  have hLpow1 : 1 ≤ (Real.log (N + 2)) ^ 20 := one_le_pow₀ hL1
  have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX1
  have hmul1 : 1 ≤ X ^ 3 * (Real.log (N + 2)) ^ 20 := by
    simpa using mul_le_mul hX3 hLpow1 (by norm_num) (by linarith)
  have hKp2 : (K : ℝ) + 2 ≤ 4 * X ^ 3 * (Real.log (N + 2)) ^ 20 := by
    have h2 : (2:ℝ) ≤ 2 * (X ^ 3 * (Real.log (N + 2)) ^ 20) := by linarith
    nlinarith [hKhi, h2]
  have hlogKp2 : Real.log ((K : ℝ) + 2) ≤ Real.log (4 * X ^ 3 * (Real.log (N + 2)) ^ 20) :=
    Real.log_le_log (by positivity) hKp2
  have hexp : Real.log (4 * X ^ 3 * (Real.log (N + 2)) ^ 20)
      = Real.log 4 + 3 * Real.log X + 20 * Real.log (Real.log (N + 2)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, Real.log_pow]
    ring
  rw [hexp] at hlogKp2
  have hlog4 : Real.log 4 ≤ Real.log N := Real.log_le_log (by norm_num) hN4
  have hfinal : Real.log ((K : ℝ) + 2) ≤ 50 * Real.log N := by linarith
  have hnn : 0 ≤ Real.log ((K : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hs := pow_le_pow_left₀ hnn hfinal 2
  have hsq : (50 * Real.log N) ^ 2 = 2500 * (Real.log N) ^ 2 := by ring
  linarith [hs, hsq]

end Work.FIArea7
