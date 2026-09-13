import Mathlib
import Submission.Commons.Analysis.Real.sum_Ico_pow_mul_le

namespace Commons.Analysis.Real

theorem sum_Ico_pow_mul_le_tail {B r θ : ℝ} {N : ℕ} (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hθ : 0 < θ) (hr : r ≤ 1 - θ / 4) (hN : B * r ^ N < θ / 48) :
    ∀ k : ℕ, N ≤ k → ∑ j ∈ Finset.Ico N k, B * r ^ j ≤ 1 / 12 := by
  intro k _
  have hbase : ∑ j ∈ Finset.Ico N k, B * r ^ j ≤ B * r ^ N / (1 - r) :=
    Commons.Analysis.Real.sum_Ico_pow_mul_le hB hr0 hr1 N k
  have h1r : 0 < 1 - r := by linarith
  have hθ4 : 0 < θ / 4 := by linarith
  have hden : θ / 4 ≤ 1 - r := by linarith
  have hBN : 0 ≤ B * r ^ N := mul_nonneg hB (pow_nonneg hr0 N)
  have hstep : B * r ^ N / (1 - r) ≤ B * r ^ N / (θ / 4) :=
    div_le_div_of_nonneg_left hBN hθ4 hden
  have hfinal : B * r ^ N / (θ / 4) ≤ 1 / 12 := by
    rw [div_le_iff₀ hθ4]
    have hkey : (1 : ℝ) / 12 * (θ / 4) = θ / 48 := by ring
    rw [hkey]
    linarith [hN]
  linarith [hbase, hstep, hfinal]

end Commons.Analysis.Real
