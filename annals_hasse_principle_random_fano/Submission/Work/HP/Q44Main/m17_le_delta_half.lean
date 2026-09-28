import Mathlib

namespace Work.HP.Q44Main

/-- From `M^(53) ≤ Δ` with `M, Δ ≥ 1` we get `M^(17) ≤ Δ^(1/2)`.

Both sides being nonnegative, raising the goal to the second power reduces it
to `M^(34) ≤ Δ`, which follows from `M^(34) ≤ M^(53) ≤ Δ` since `M ≥ 1` and
`34 ≤ 53`. -/
theorem m17_le_delta_half (M Δ : ℝ) (hM : 1 ≤ M) (hΔ : 1 ≤ Δ)
    (hMle : M^(53:ℝ) ≤ Δ) :
    M^(17:ℝ) ≤ Δ^((1:ℝ)/2) := by
  have hM0 : (0:ℝ) ≤ M := le_trans zero_le_one hM
  have hΔ0 : (0:ℝ) ≤ Δ := le_trans zero_le_one hΔ
  -- `M^(34) ≤ M^(53) ≤ Δ`
  have key : M^(34:ℝ) ≤ Δ :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hM (by norm_num)) hMle
  -- raise both sides of the goal to the power `2` (an equivalence, both sides ≥ 0)
  rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hΔ0 _)
        (by norm_num : (0:ℝ) < 2)]
  rw [← Real.rpow_mul hM0 17 2, ← Real.rpow_mul hΔ0 ((1:ℝ)/2) 2]
  norm_num
  simpa using key

end Work.HP.Q44Main
