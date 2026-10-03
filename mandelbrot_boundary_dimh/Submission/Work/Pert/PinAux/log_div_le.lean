import Mathlib

namespace Work.Pert.PinAux

theorem log_div_le (z : ℂ) (M mz B R₁ : ℝ) (hB : 0 ≤ B) (hR₁ : 0 < R₁) (hmz : R₁ ≤ mz)
    (hMpos : 0 < M) (hM : M ≤ |z.im| + B) :
    Real.log (M / mz) ≤ (1 + B) / R₁ + Real.log (2 + ‖z‖) := by
  have hmzpos : 0 < mz := lt_of_lt_of_le hR₁ hmz
  have hnorm : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  -- `M` is bounded by `‖z‖ + B`, hence positive
  have hMz : M ≤ ‖z‖ + B := le_trans hM (by linarith [Complex.abs_im_le_norm z])
  have hxBpos : 0 < ‖z‖ + B := lt_of_lt_of_le hMpos hMz
  -- enlarge `M` to `‖z‖ + B`: monotonicity of `log` on positives
  have h1 : Real.log (M / mz) ≤ Real.log ((‖z‖ + B) / mz) :=
    Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right hMz (le_of_lt hmzpos))
  -- enlarge `mz` down to `R₁`
  have h2 : Real.log ((‖z‖ + B) / mz) ≤ Real.log ((‖z‖ + B) / R₁) :=
    Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_left (le_of_lt hxBpos) hR₁ hmz)
  have hden : 0 < (‖z‖ + B) / ((2 + ‖z‖) * R₁) := by positivity
  -- `(‖z‖ + B)/(2 + ‖z‖) ≤ 1 + B`
  have hq : (‖z‖ + B) / (2 + ‖z‖) ≤ 1 + B := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hB, hnorm]
  have hle : (‖z‖ + B) / ((2 + ‖z‖) * R₁) ≤ (1 + B) / R₁ := by
    have := div_le_div_of_nonneg_right hq (le_of_lt hR₁)
    simpa [div_div] using this
  -- `log y ≤ y - 1`
  have key : Real.log ((‖z‖ + B) / ((2 + ‖z‖) * R₁)) ≤ (1 + B) / R₁ :=
    le_trans (Real.log_le_sub_one_of_pos hden) (by linarith)
  have hlogeq : Real.log ((‖z‖ + B) / R₁)
      = Real.log ((‖z‖ + B) / ((2 + ‖z‖) * R₁)) + Real.log (2 + ‖z‖) := by
    rw [show (‖z‖ + B) / R₁ = ((‖z‖ + B) / ((2 + ‖z‖) * R₁)) * (2 + ‖z‖) from by
      field_simp]
    rw [Real.log_mul (by positivity) (by positivity)]
  linarith [h1, h2, hlogeq, key]

end Work.Pert.PinAux
