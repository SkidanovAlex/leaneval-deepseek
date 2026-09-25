import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs

namespace Work.RHContract.A.regionII.netGain

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Elementary bounds on `√ξ` for `ξ ∈ [10^5, 10^8)`. -/
theorem sqrt_xi_bounds (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) (hhi : ξ < (10 : ℝ) ^ 8) :
    (316 : ℝ) ≤ Real.sqrt ξ ∧ Real.sqrt ξ < 10000 := by
  have hξpos : 0 < ξ := by linarith
  refine ⟨?_, ?_⟩
  · rw [Real.le_sqrt (by norm_num) (le_of_lt hξpos)]
    nlinarith [hlo]
  · rw [Real.sqrt_lt (le_of_lt hξpos) (by norm_num)]
    norm_num at hhi ⊢
    linarith

/-- `log ξ ≥ 11.5` for `ξ ≥ 10^5`. -/
theorem log_xi_ge (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) : (11.5 : ℝ) ≤ Real.log ξ := by
  have h1 : Real.log (100000:ℝ) ≤ Real.log ξ := Real.log_le_log (by norm_num) hlo
  have h2 : Real.log (100000:ℝ) = 5 * (Real.log 2 + Real.log 5) := by
    rw [show (100000:ℝ) = 10^5 by norm_num, Real.log_pow, Real.log_ten_eq]
    norm_num
  have h2' : (2.3025850926:ℝ) ≤ Real.log 2 + Real.log 5 := by
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  linarith

/-- The certificate `√2 · (1 − log 2/(2 log ξ)) ≥ 1.37` for `ξ ≥ 10^5`. -/
theorem sqrt2_factor_ge (ξ : ℝ) (hlog : (11.5 : ℝ) ≤ Real.log ξ) :
    (1.37 : ℝ) ≤ Real.sqrt 2 * (1 - Real.log 2 / (2 * Real.log ξ)) := by
  have hfac : (0.9688 : ℝ) ≤ 1 - Real.log 2 / (2 * Real.log ξ) := by
    have hlog2_le : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]
    have hden : 0 < 2 * Real.log ξ := by linarith
    have hratio : Real.log 2 / (2 * Real.log ξ) ≤ 0.6932 / 23 := by
      rw [div_le_div_iff₀ hden (by norm_num)]
      nlinarith [hlog2_le, hlog]
    linarith
  have hs2_le : (1.41421 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hmul : (1.41421 : ℝ) * 0.9688 ≤ Real.sqrt 2 * (1 - Real.log 2 / (2 * Real.log ξ)) :=
    mul_le_mul hs2_le hfac (by norm_num) (Real.sqrt_nonneg 2)
  nlinarith [hmul]

/-- `430 ≤ netQlo ξ` for `ξ ∈ [10^5, 10^8)`. -/
theorem netQlo_ge (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) (hhi : ξ < (10 : ℝ) ^ 8) :
    (430 : ℝ) ≤ netQlo ξ := by
  have hs_ge : (316 : ℝ) ≤ Real.sqrt ξ := (sqrt_xi_bounds ξ hlo hhi).1
  have hF := sqrt2_factor_ge ξ (log_xi_ge ξ hlo)
  rw [netQlo]
  have h1 : (316:ℝ) * 1.37 ≤ Real.sqrt ξ * (Real.sqrt 2 * (1 - Real.log 2/(2*Real.log ξ))) :=
    mul_le_mul hs_ge hF (by norm_num) (Real.sqrt_nonneg ξ)
  calc (430:ℝ) ≤ 316 * 1.37 := by norm_num
    _ ≤ Real.sqrt ξ * (Real.sqrt 2 * (1 - Real.log 2/(2*Real.log ξ))) := h1
    _ = Real.sqrt 2 * Real.sqrt ξ * (1 - Real.log 2/(2*Real.log ξ)) := by ring

/-- `(115/100)·√ξ + 1 ≤ netQlo ξ` for `ξ ∈ [10^5, 10^8)`. -/
theorem netQlo_ge_pf (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) (hhi : ξ < (10 : ℝ) ^ 8) :
    (115/100 : ℝ) * Real.sqrt ξ + 1 ≤ netQlo ξ := by
  have hs_ge : (316 : ℝ) ≤ Real.sqrt ξ := (sqrt_xi_bounds ξ hlo hhi).1
  have hF := sqrt2_factor_ge ξ (log_xi_ge ξ hlo)
  rw [netQlo]
  have hFm : (0.22:ℝ) ≤ Real.sqrt 2*(1 - Real.log 2/(2*Real.log ξ)) - 1.15 := by linarith [hF]
  have h0 : (0:ℝ) ≤ Real.sqrt ξ := Real.sqrt_nonneg ξ
  have key : Real.sqrt ξ * 0.22 ≤
      Real.sqrt ξ * (Real.sqrt 2*(1 - Real.log 2/(2*Real.log ξ)) - 1.15) :=
    mul_le_mul_of_nonneg_left hFm h0
  have hs2 : (316:ℝ)*0.22 ≤ Real.sqrt ξ * 0.22 := mul_le_mul_of_nonneg_right hs_ge (by norm_num)
  nlinarith [key, hs2]

/-- `netQlo ξ < 14143` for `ξ ∈ [10^5, 10^8)`. -/
theorem netQlo_lt (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) (hhi : ξ < (10 : ℝ) ^ 8) :
    netQlo ξ < 14143 := by
  have hs_lt : Real.sqrt ξ < 10000 := (sqrt_xi_bounds ξ hlo hhi).2
  rw [netQlo]
  have hlog_pos : 0 < Real.log ξ := by linarith [log_xi_ge ξ hlo]
  have hc_nonneg : 0 ≤ Real.log 2 / (2 * Real.log ξ) := by positivity
  have hfac_le1 : 1 - Real.log 2 / (2 * Real.log ξ) ≤ 1 := by linarith
  have hs2_lt : Real.sqrt 2 < 1.414214 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  calc Real.sqrt 2 * Real.sqrt ξ * (1 - Real.log 2 / (2 * Real.log ξ))
      ≤ Real.sqrt 2 * Real.sqrt ξ * 1 := by
        apply mul_le_mul_of_nonneg_left hfac_le1; positivity
    _ = Real.sqrt 2 * Real.sqrt ξ := by ring
    _ < Real.sqrt 2 * 10000 := mul_lt_mul_of_pos_left hs_lt (Real.sqrt_pos.mpr (by norm_num))
    _ < 14143 := by nlinarith [hs2_lt]

theorem floorBounds (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) (hhi : ξ < (10 : ℝ) ^ 8) :
    430 ≤ netNf ξ ∧ netNf ξ ≤ 14142 ∧ 360 ≤ netPf ξ ∧ netPf ξ ≤ 12000 ∧ netPf ξ < netNf ξ := by
  have hs := sqrt_xi_bounds ξ hlo hhi
  have hQlo_ge : (430 : ℝ) ≤ netQlo ξ := netQlo_ge ξ hlo hhi
  have hQlo_strict : (115/100 : ℝ) * Real.sqrt ξ + 1 ≤ netQlo ξ := netQlo_ge_pf ξ hlo hhi
  have hQlo_lt : netQlo ξ < 14143 := netQlo_lt ξ hlo hhi
  have hQlo_nonneg : 0 ≤ netQlo ξ := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [netNf]; exact Nat.le_floor hQlo_ge
  · have h : netNf ξ < 14143 := by
      rw [netNf]
      exact (Nat.floor_lt hQlo_nonneg).mpr hQlo_lt
    omega
  · rw [netPf]; apply Nat.le_floor; nlinarith [hs.1]
  · have hlt : netPf ξ < 12001 := by
      rw [netPf]
      exact (Nat.floor_lt (by positivity)).mpr (by nlinarith [hs.2])
    omega
  · have h1 : (115/100 : ℝ) * Real.sqrt ξ ≤ netQlo ξ - 1 := by linarith
    have h2 : ⌊(115/100 : ℝ) * Real.sqrt ξ⌋₊ ≤ ⌊netQlo ξ - 1⌋₊ := Nat.floor_mono h1
    have h3 : ⌊netQlo ξ - 1⌋₊ = ⌊netQlo ξ⌋₊ - 1 := Nat.floor_sub_one _
    have h2' : ⌊(115/100 : ℝ) * Real.sqrt ξ⌋₊ ≤ ⌊netQlo ξ⌋₊ - 1 := by rw [h3] at h2; exact h2
    rw [netPf, netNf]
    have hc : 0 < ⌊netQlo ξ⌋₊ := lt_of_lt_of_le (by norm_num) (Nat.le_floor hQlo_ge)
    exact Nat.lt_of_le_pred hc h2'

end Work.RHContract.A.regionII.netGain
