import Submission.Commons.Analysis.Real.exp_sub_one_sub_le

namespace Commons.Analysis.Real

/-- Elementary consequence of `exp_sub_one_sub_le`: for `u ≥ 0`,
`(1 - u / 3) * (exp u - 1 - u) ≤ u ^ 2 / 2`. -/
private lemma one_sub_div_three_mul_exp_sub_one_sub_le {u : ℝ} (hu : 0 ≤ u) :
    (1 - u / 3) * (Real.exp u - 1 - u) ≤ u ^ 2 / 2 := by
  have hexp : 0 ≤ Real.exp u - 1 - u := by
    have h := Real.add_one_le_exp u
    linarith
  rcases lt_or_ge u 3 with h3 | h3
  · have hle := exp_sub_one_sub_le hu h3
    have hcoef : 0 ≤ 1 - u / 3 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hle hcoef
    calc (1 - u / 3) * (Real.exp u - 1 - u)
        ≤ (1 - u / 3) * (u ^ 2 / (2 * (1 - u / 3))) := hmul
      _ = u ^ 2 / 2 := by field_simp
  · have hcoef : 1 - u / 3 ≤ 0 := by linarith
    have h1 : (1 - u / 3) * (Real.exp u - 1 - u) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoef hexp
    have h2 : 0 ≤ u ^ 2 / 2 := by positivity
    linarith

theorem mul_exp_sub_one_sub_le {B τ μ : ℝ} (hB : 0 < B) (hτ : 0 ≤ τ) (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ B - τ / 3) :
    μ * (Real.exp (τ / B) - 1 - τ / B) ≤ (τ / B) * τ / 2 := by
  have hBne : B ≠ 0 := ne_of_gt hB
  have hBpos : 0 ≤ B := le_of_lt hB
  have ht : 0 ≤ τ / B := div_nonneg hτ hBpos
  have hexpnn : 0 ≤ Real.exp (τ / B) - 1 - τ / B := by
    have h := Real.add_one_le_exp (τ / B)
    linarith
  -- Step 1: multiply `hμ` by the nonnegative factor.
  have hstep1 : μ * (Real.exp (τ / B) - 1 - τ / B)
      ≤ (B - τ / 3) * (Real.exp (τ / B) - 1 - τ / B) :=
    mul_le_mul_of_nonneg_right hμ hexpnn
  -- Step 2: bound the `(B - τ / 3)` term.
  have haux := one_sub_div_three_mul_exp_sub_one_sub_le ht
  have hBm := mul_le_mul_of_nonneg_left haux hBpos
  have h1 : B * ((1 - (τ / B) / 3) * (Real.exp (τ / B) - 1 - τ / B))
      = (B - τ / 3) * (Real.exp (τ / B) - 1 - τ / B) := by
    field_simp
  have h2 : B * ((τ / B) ^ 2 / 2) = (τ / B) * τ / 2 := by
    field_simp
  rw [h1, h2] at hBm
  linarith

end Commons.Analysis.Real
