import Mathlib
import Submission.Work.MassTransferenceAlt.Basic

namespace Work.MassTransferenceAlt.Kgb

/-- Elementary numeric input for the mass-transference step: given `16 δ ≤ r` one can pick a
scale `e = min (ε/2) (((δ/2)^(1/d))/2)` which is positive, at most `ε`, whose `d`-th power is
controlled by `δ/2^(d+1)`, and for which `8 e^d ≤ r/4`. -/
theorem eps_arith (d δ ε r : ℝ) (hd : 0 < d) (hδ : 0 < δ) (hε : 0 < ε) (hr : 0 < r)
    (h16 : 16 * δ ≤ r) :
    let e : ℝ := min (ε / 2) (((δ / 2) ^ (1 / d)) / 2)
    0 < e ∧ e ≤ ε ∧ e ^ d ≤ δ / 2 ^ (d + 1) ∧ 8 * e ^ d ≤ r / 4 := by
  change 0 < min (ε / 2) (((δ / 2) ^ (1 / d)) / 2) ∧
    min (ε / 2) (((δ / 2) ^ (1 / d)) / 2) ≤ ε ∧
    (min (ε / 2) (((δ / 2) ^ (1 / d)) / 2)) ^ d ≤ δ / 2 ^ (d + 1) ∧
    8 * (min (ε / 2) (((δ / 2) ^ (1 / d)) / 2)) ^ d ≤ r / 4
  have hδ2 : 0 < δ / 2 := by linarith
  have hApos : (0 : ℝ) < (δ / 2) ^ (1 / d) := Real.rpow_pos_of_pos hδ2 _
  have hBpos : 0 < ((δ / 2) ^ (1 / d)) / 2 := div_pos hApos (by norm_num)
  have hepos : 0 < min (ε / 2) (((δ / 2) ^ (1 / d)) / 2) := lt_min (by linarith) hBpos
  have heε : min (ε / 2) (((δ / 2) ^ (1 / d)) / 2) ≤ ε :=
    le_trans (min_le_left _ _) (by linarith)
  have heB : min (ε / 2) (((δ / 2) ^ (1 / d)) / 2) ≤ ((δ / 2) ^ (1 / d)) / 2 :=
    min_le_right _ _
  have hmono : (min (ε / 2) (((δ / 2) ^ (1 / d)) / 2)) ^ d
      ≤ (((δ / 2) ^ (1 / d)) / 2) ^ d :=
    Real.rpow_le_rpow (le_of_lt hepos) heB (le_of_lt hd)
  have hBeq : (((δ / 2) ^ (1 / d)) / 2) ^ d = δ / 2 ^ (d + 1) := by
    rw [Real.div_rpow (le_of_lt hApos) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_mul (le_of_lt hδ2) (1 / d) d]
    have h1 : 1 / d * d = 1 := by field_simp
    rw [h1, Real.rpow_one]
    have h2 : (2 : ℝ) ^ (d + 1) = (2 : ℝ) ^ d * 2 := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    rw [h2]
    field_simp
  have hge : (2 : ℝ) ≤ 2 ^ (d + 1) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : (1 : ℝ) ≤ d + 1)
    rwa [Real.rpow_one] at h
  have hd2 : (min (ε / 2) (((δ / 2) ^ (1 / d)) / 2)) ^ d ≤ δ / 2 := by
    calc (min (ε / 2) (((δ / 2) ^ (1 / d)) / 2)) ^ d
        ≤ (((δ / 2) ^ (1 / d)) / 2) ^ d := hmono
      _ = δ / 2 ^ (d + 1) := hBeq
      _ ≤ δ / 2 := div_le_div_of_nonneg_left (le_of_lt hδ) (by norm_num : (0 : ℝ) < 2) hge
  refine ⟨hepos, heε, ?_, ?_⟩
  · calc (min (ε / 2) (((δ / 2) ^ (1 / d)) / 2)) ^ d
        ≤ (((δ / 2) ^ (1 / d)) / 2) ^ d := hmono
      _ = δ / 2 ^ (d + 1) := hBeq
  · have h8 : 8 * (min (ε / 2) (((δ / 2) ^ (1 / d)) / 2)) ^ d ≤ 8 * (δ / 2) :=
      mul_le_mul_of_nonneg_left hd2 (by norm_num : (0 : ℝ) ≤ 8)
    nlinarith [h8, h16]

end Work.MassTransferenceAlt.Kgb
