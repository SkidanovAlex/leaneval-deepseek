import Mathlib

namespace Work.KMTAreas.A7

/-- **The uniform shift majorant.**  If `0 ≤ M` and `|c| ≤ M`, then for *every* integer `j` the
shifted rational kernel `1/(1 + |j - c|)^2` is dominated by the fixed summable majorant
`(2M+1)^2 / (1 + |j|)^2`, uniformly over the shift `c ∈ [-M, M]`.

Proof (no case split needed for the affine form, as both denominators are positive):
`1 + |j| ≤ 1 + |j - c| + |c| ≤ 1 + |j-c| + M` (`abs_add_le`),
and since `1 + |j-c| ≥ 1` and `M ≥ 0`,
`1 + |j-c| + M ≤ (2M+1)(1 + |j-c|)`.
Squaring and using `div_le_div_iff₀` (with `0 < 1 + |j-c|` and `0 < 1 + |j|`) gives the claim. -/
theorem one_div_sq_le_of_abs_sub_le {c M : ℝ} (hM : 0 ≤ M) (hc : |c| ≤ M) (j : ℤ) :
    1 / (1 + |(j : ℝ) - c|) ^ 2 ≤ (2 * M + 1) ^ 2 / (1 + |(j : ℝ)|) ^ 2 := by
  have hjc : |(j : ℝ)| ≤ |(j : ℝ) - c| + M := by
    have h1 : |(j : ℝ)| ≤ |(j : ℝ) - c| + |c| := by
      have h := abs_add_le ((j : ℝ) - c) c
      have h2 : ((j : ℝ) - c) + c = (j : ℝ) := by ring
      rwa [h2] at h
    linarith
  have hposn : 0 < 1 + |(j : ℝ)| := by positivity
  have hposd : 0 < 1 + |(j : ℝ) - c| := by positivity
  have key : (1 + |(j : ℝ)|) ≤ (2 * M + 1) * (1 + |(j : ℝ) - c|) := by
    have ha : 0 ≤ |(j : ℝ) - c| := abs_nonneg _
    have h3 : 1 + (|(j : ℝ) - c| + M) ≤ (2 * M + 1) * (1 + |(j : ℝ) - c|) := by nlinarith
    linarith
  have hsq : (1 + |(j : ℝ)|) ^ 2 ≤ ((2 * M + 1) * (1 + |(j : ℝ) - c|)) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hposn) key 2
  rw [mul_pow] at hsq
  rw [div_le_div_iff₀ (pow_pos hposd 2) (pow_pos hposn 2)]
  linarith

end Work.KMTAreas.A7
