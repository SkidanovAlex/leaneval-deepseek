import Mathlib

namespace Work.KMTAreas.SupNorm

/-- For `C, D ≥ 0`, `a > 0` and `ε > 0` there is a small `δ ∈ (0, 1]` with `D * δ ≤ 1`
and `C * δ ^ a ≤ ε`. -/
theorem exists_delta_rpow_mul_le {C a D ε : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hD : 0 ≤ D)
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ D * δ ≤ 1 ∧ C * δ ^ a ≤ ε := by
  refine ⟨min 1 (min (1/(D+1)) ((ε/(C+1))^(1/a))), ?_, ?_, ?_, ?_⟩
  · refine lt_min one_pos (lt_min ?_ ?_)
    · positivity
    · exact Real.rpow_pos_of_pos (by positivity) _
  · exact min_le_left ..
  · have hle : min 1 (min (1/(D+1)) ((ε/(C+1))^(1/a))) ≤ 1/(D+1) :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hD1 : (0:ℝ) < D + 1 := by linarith
    have h2 : D * (1/(D+1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hD1]; linarith
    exact le_trans (mul_le_mul_of_nonneg_left hle hD) h2
  · have hδpos : 0 < min 1 (min (1/(D+1)) ((ε/(C+1))^(1/a))) := by
      refine lt_min one_pos (lt_min ?_ ?_)
      · positivity
      · exact Real.rpow_pos_of_pos (by positivity) _
    have hxC : (0:ℝ) < ε/(C+1) := by positivity
    have hle : min 1 (min (1/(D+1)) ((ε/(C+1))^(1/a))) ≤ (ε/(C+1))^(1/a) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have h1 : (min 1 (min (1/(D+1)) ((ε/(C+1))^(1/a))))^a
        ≤ ((ε/(C+1))^(1/a))^a := Real.rpow_le_rpow (le_of_lt hδpos) hle ha.le
    have h2 : ((ε/(C+1))^(1/a))^a = ε/(C+1) := by
      rw [← Real.rpow_mul (le_of_lt hxC), one_div_mul_cancel ha.ne', Real.rpow_one]
    have h5 : C * (min 1 (min (1/(D+1)) ((ε/(C+1))^(1/a))))^a ≤ C * (ε/(C+1)) :=
      mul_le_mul_of_nonneg_left (h1.trans h2.le) hC
    have hC1 : (0:ℝ) < C + 1 := by linarith
    have h6 : C * (ε/(C+1)) ≤ ε := by
      have hCdiv : C / (C+1) ≤ 1 := by rw [div_le_one hC1]; linarith
      calc C * (ε/(C+1)) = ε * (C/(C+1)) := by ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hCdiv hε.le
        _ = ε := by ring
    linarith

end Work.KMTAreas.SupNorm
