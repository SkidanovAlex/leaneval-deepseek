import Mathlib
import Submission.Work.FIArea2.vol_bound_defs

namespace Work.FIArea2

/-- `volT` exceeds `volS = min volR volT` by at most `(1-γ²)^{-1/4}`, i.e. the logarithmic
loss in the threshold ratio is at most `(1/4)·log(1/(1-γ²))`.

Here `C = 4√M/√(1-γ²)` is the critical radius of the ellipse bound, so that
`volT M C ^ 2 = (C + 2√M)/2 = √M·(2/√(1-γ²) + 1)` and `volR M ^ 2 = 4√M`, whence
`(volT/volR)^2 = (2/√(1-γ²) + 1)/4 ≤ 1/√(1-γ²)` because `√(1-γ²) ≤ 1 ≤ 2`.  Thus
`volT/volR ≤ (1/√(1-γ²))^{1/2} = (1-γ²)^{-1/4}`, whose logarithm is `(1/4)log(1/(1-γ²))`.
Since `volS` is the smaller of `volR` and `volT`, the ratio `volT/volS` is either `1` (when
`volT ≤ volR`) or `volT/volR` (when `volR ≤ volT`); both are bounded as claimed. -/
theorem log_volT_div_volS_le (M γ : ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    Real.log (volT M (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) /
        volS M (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)))
      ≤ (1 / 4) * Real.log (1 / (1 - γ ^ 2)) := by
  have ha_pos : 0 < 1 - γ ^ 2 := by nlinarith [sq_nonneg γ, sq_nonneg (1 - γ)]
  have ha_le_one : 1 - γ ^ 2 ≤ 1 := by nlinarith [sq_nonneg γ]
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  -- rename the critical radius
  set C : ℝ := 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) with hC
  have hT_pos : 0 < volT M C := volT_pos M C (by positivity)
  have hR_pos : 0 < volR M := volR_pos M hMpos
  -- the logarithm of the target factor `(1/√(1-γ²))^{1/2} = (1-γ²)^{-1/4}`
  have hlogeq : Real.log (Real.sqrt (1 / Real.sqrt (1 - γ ^ 2)))
      = (1 / 4) * Real.log (1 / (1 - γ ^ 2)) := by
    have h1 : 1 / Real.sqrt (1 - γ ^ 2) = Real.sqrt (1 / (1 - γ ^ 2)) := by
      simp only [one_div]
      rw [Real.sqrt_inv]
    rw [h1, Real.log_sqrt (Real.sqrt_nonneg _),
      Real.log_sqrt (by positivity : (0 : ℝ) ≤ 1 / (1 - γ ^ 2))]
    ring
  -- the right-hand side is nonnegative
  have hRHS : 0 ≤ (1 / 4) * Real.log (1 / (1 - γ ^ 2)) := by
    have h1 : 1 ≤ 1 / (1 - γ ^ 2) := (one_le_div ha_pos).mpr ha_le_one
    have := Real.log_nonneg h1
    linarith
  -- `volT ^ 2 = √M·(2/√(1-γ²) + 1)` at the critical radius
  have hTsq : volT M C ^ 2 = Real.sqrt M * (2 / Real.sqrt (1 - γ ^ 2) + 1) := by
    rw [volT_sq M C (by positivity), hC]
    field_simp
    ring
  have hRsq : volR M ^ 2 = 4 * Real.sqrt M := volR_sq M (le_of_lt hMpos)
  have hratio_sq : (volT M C / volR M) ^ 2 = (2 / Real.sqrt (1 - γ ^ 2) + 1) / 4 := by
    rw [div_pow, hTsq, hRsq]
    field_simp
  -- `(volT/volR)^2 ≤ 1/√(1-γ²)`
  have hsq_le : (volT M C / volR M) ^ 2 ≤ 1 / Real.sqrt (1 - γ ^ 2) := by
    rw [hratio_sq]
    have hb2 : Real.sqrt (1 - γ ^ 2) ≤ 2 := by
      have := Real.sqrt_le_one.mpr ha_le_one
      linarith
    have he : 1 / Real.sqrt (1 - γ ^ 2) - (2 / Real.sqrt (1 - γ ^ 2) + 1) / 4
        = (2 - Real.sqrt (1 - γ ^ 2)) / (4 * Real.sqrt (1 - γ ^ 2)) := by
      field_simp
      ring
    have hnn : 0 ≤ (2 - Real.sqrt (1 - γ ^ 2)) / (4 * Real.sqrt (1 - γ ^ 2)) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  -- hence `volT/volR ≤ (1-γ²)^{-1/4}`
  have hratio_le : volT M C / volR M ≤ Real.sqrt (1 / Real.sqrt (1 - γ ^ 2)) := by
    rw [← Real.sqrt_sq (le_of_lt (div_pos hT_pos hR_pos))]
    exact Real.sqrt_le_sqrt hsq_le
  have hlog : Real.log (volT M C / volR M) ≤ (1 / 4) * Real.log (1 / (1 - γ ^ 2)) := by
    have h := Real.log_le_log (div_pos hT_pos hR_pos) hratio_le
    rwa [hlogeq] at h
  -- `volS` is the smaller of `volR` and `volT`
  by_cases hle : volT M C ≤ volR M
  · have hS : volS M C = volT M C := by
      rw [volS_eq, min_eq_right hle]
    rw [hS, div_self (ne_of_gt hT_pos), Real.log_one]
    exact hRHS
  · have hS : volS M C = volR M := by
      rw [volS_eq, min_eq_left (le_of_lt (not_le.mp hle))]
    rw [hS]
    exact hlog

end Work.FIArea2
