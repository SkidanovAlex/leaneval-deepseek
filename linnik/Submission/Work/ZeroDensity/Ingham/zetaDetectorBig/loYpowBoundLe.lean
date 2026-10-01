import Mathlib
import Submission.Work.ZeroDensity.Ingham.loYpowBound

namespace Work.ZeroDensity.Ingham.zetaDetectorBig

/-- Same shape as `loYpowBound` but with the non-strict hypothesis
`σ ≤ 1/2 + 1/(2 log (A*T))`. -/
theorem loYpowBoundLe :
    ∃ C : ℝ, 0 < C ∧ ∀ (A T K σ Y : ℝ), 6 ≤ A → 2 ≤ T → 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
      σ ≤ 1 / 2 + 1 / (2 * Real.log (A * T)) →
      (2 * T + 1) ≤
        C * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) := by
  refine ⟨3 * Real.exp (4 / 3), by positivity, ?_⟩
  intro A T K σ Y hA hT hK hY hYT hσ
  have hAT_gt1 : (1 : ℝ) < A * T := by nlinarith
  have hATpos : 0 < A * T := by linarith
  have hLpos : 0 < Real.log (A * T) := Real.log_pos hAT_gt1
  have hLne : Real.log (A * T) ≠ 0 := ne_of_gt hLpos
  have h2Lne : 2 * Real.log (A * T) ≠ 0 := mul_ne_zero (by norm_num) hLne
  have h3Lne : 3 * Real.log (A * T) ≠ 0 := mul_ne_zero (by norm_num) hLne
  have hTpos : 0 < T := by linarith
  have hTKpos : 0 < T + K := by linarith
  have hYpos : 0 < Y := by linarith
  have hlogYnn : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hlogY2L : Real.log Y ≤ 2 * Real.log (A * T) := by
    have h1 : Real.log Y ≤ Real.log ((A * T) ^ 2) := Real.log_le_log hYpos hYT
    have h2 : Real.log ((A * T) ^ 2) = 2 * Real.log (A * T) := by
      have hmul : (A * T) ^ 2 = (A * T) * (A * T) := by ring
      rw [hmul, Real.log_mul (ne_of_gt hATpos) (ne_of_gt hATpos)]
      ring
    linarith
  have he : (-2 : ℝ) / (3 * Real.log (A * T)) ≤ (2 - 4 * σ) / 3 := by
    have h1 : 4 * σ ≤ 2 + 2 / Real.log (A * T) := by
      have hmul : 4 * σ ≤ 4 * (1 / 2 + 1 / (2 * Real.log (A * T))) := by linarith
      have heq : 4 * (1 / 2 + 1 / (2 * Real.log (A * T))) = 2 + 2 / Real.log (A * T) := by
        field_simp [hLne, h2Lne, h3Lne]
        ring
      linarith
    have h2 : (-2 : ℝ) / Real.log (A * T) ≤ 2 - 4 * σ := by
      have e : (-2 : ℝ) / Real.log (A * T) = -(2 / Real.log (A * T)) := by ring
      linarith [h1, e]
    have h3 : ((-2 : ℝ) / Real.log (A * T)) / 3 ≤ (2 - 4 * σ) / 3 :=
      div_le_div_of_nonneg_right h2 (by norm_num)
    have heq : ((-2 : ℝ) / Real.log (A * T)) / 3 = (-2 : ℝ) / (3 * Real.log (A * T)) := by
      rw [div_div, mul_comm (Real.log (A * T)) 3]
    rwa [heq] at h3
  have hkey : -4 / 3 ≤ ((2 - 4 * σ) / 3) * Real.log Y := by
    have step1 : ((-2 : ℝ) / (3 * Real.log (A * T))) * Real.log Y ≤ ((2 - 4 * σ) / 3) * Real.log Y :=
      mul_le_mul_of_nonneg_right he hlogYnn
    have step2 : -4 / 3 ≤ ((-2 : ℝ) / (3 * Real.log (A * T))) * Real.log Y := by
      have hneg : (-2 : ℝ) / (3 * Real.log (A * T)) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · norm_num
        · positivity
      have hml := mul_le_mul_of_nonpos_left hlogY2L hneg
      have e1 : (2 * Real.log (A * T)) * ((-2 : ℝ) / (3 * Real.log (A * T))) = -4 / 3 := by
        field_simp [hLne, h2Lne, h3Lne]
        ring
      have e2 : Real.log Y * ((-2 : ℝ) / (3 * Real.log (A * T)))
              = ((-2 : ℝ) / (3 * Real.log (A * T))) * Real.log Y := by ring
      linarith [hml, e1, e2]
    linarith [step1, step2]
  have hYexp : Real.exp (-4 / 3) ≤ Y ^ ((2 - 4 * σ) / 3) := by
    rw [Real.rpow_def_of_pos hYpos, Real.exp_le_exp]
    rw [mul_comm (Real.log Y) ((2 - 4 * σ) / 3)]
    exact hkey
  have hTprod : T ≤ T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) := by
    have h1 : T ^ ((2 : ℝ) / 3) ≤ (T + K) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (le_of_lt hTpos) (by linarith) (by norm_num)
    have h2 : T ^ ((1 : ℝ) / 3) * T ^ ((2 : ℝ) / 3) = T := by
      rw [← Real.rpow_add hTpos]
      rw [show (1 : ℝ) / 3 + (2 : ℝ) / 3 = 1 by norm_num, Real.rpow_one]
    calc T = T ^ ((1 : ℝ) / 3) * T ^ ((2 : ℝ) / 3) := h2.symm
      _ ≤ T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.rpow_pos_of_pos hTpos _))
  have hPpos : 0 < T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) :=
    mul_pos (Real.rpow_pos_of_pos hTpos _) (Real.rpow_pos_of_pos hTKpos _)
  have hmain : T * Real.exp (-4 / 3) ≤
      T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) := by
    have hA' : T * Real.exp (-4 / 3) ≤
        (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) * Real.exp (-4 / 3) :=
      mul_le_mul_of_nonneg_right hTprod (le_of_lt (Real.exp_pos _))
    have hB' : (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) * Real.exp (-4 / 3) ≤
        (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) * Y ^ ((2 - 4 * σ) / 3) :=
      mul_le_mul_of_nonneg_left hYexp (le_of_lt hPpos)
    linarith [hA', hB']
  have hCpos : (0 : ℝ) < 3 * Real.exp (4 / 3) := by positivity
  have hexp : Real.exp (4 / 3) * Real.exp (-4 / 3) = 1 := by
    rw [← Real.exp_add, show (4 : ℝ) / 3 + (-4 / 3) = 0 by norm_num, Real.exp_zero]
  have hCbound : (3 * Real.exp (4 / 3)) * (T * Real.exp (-4 / 3)) = 3 * T := by
    have hh : (3 * Real.exp (4 / 3)) * (T * Real.exp (-4 / 3))
        = 3 * T * (Real.exp (4 / 3) * Real.exp (-4 / 3)) := by ring
    rw [hh, hexp]; ring
  have h2 : 3 * T ≤ (3 * Real.exp (4 / 3)) *
      (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) := by
    have h := mul_le_mul_of_nonneg_left hmain (le_of_lt hCpos)
    rwa [hCbound] at h
  linarith [h2, hT]

end Work.ZeroDensity.Ingham.zetaDetectorBig
