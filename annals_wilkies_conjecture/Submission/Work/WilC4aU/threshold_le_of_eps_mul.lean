import Mathlib
import Submission.Work.WilC4aU.Defs

namespace Work.WilC4aU

/-- Bookkeeping: from the cluster-condition scale `1 ≤ ε * x` and `ε ≤ 1 / (max R 1 + 1)`,
the point `x` is past the asymptotic threshold `R`, and `x ≥ 1`. -/
theorem threshold_le_of_eps_mul {R ε x : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / (max R 1 + 1))
    (hx : 1 ≤ ε * x) : R ≤ x ∧ 1 ≤ x := by
  have hm1 : (0:ℝ) < max R 1 + 1 := by
    have : (1:ℝ) ≤ max R 1 := le_max_right _ _
    linarith
  have hkey : max R 1 + 1 ≤ 1 / ε := by
    rw [le_div_iff₀ hε]
    have h2 : ε * (max R 1 + 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hεle (le_of_lt hm1)
      rwa [div_mul_cancel₀ _ (ne_of_gt hm1)] at this
    linarith [h2]
  have hx2 : 1 / ε ≤ x := by
    rw [div_le_iff₀ hε]
    linarith [hx]
  constructor
  · have : R ≤ max R 1 := le_max_left _ _
    linarith
  · have : (1:ℝ) ≤ max R 1 := le_max_right _ _
    linarith

end Work.WilC4aU
