import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.regionII.theta_deficit_bound
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.A.regionII.caC1_lower_B
import Submission.Work.RHContract.A.regionII.caNet2_nonneg_B
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.A.regionII

/-- Region II (`10^5 ≤ ξ(ε) < 10^8`) lower bound for `caC1 + caNet2`.

`caC1 ε ≥ (43/100)·u(ξ)` (`caC1_lower_B`) and `caNet2 ε ≥ 0` (`caNet2_nonneg_B`),
where `u(ξ) = caU ξ = 1/(√ξ log ξ)`. -/
theorem caC1_add_caNet2_lower_B (ε : ℝ) (hε : 0 < ε)
    (hlo : 100000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < (10:ℝ)^8)
    (hθ : ∀ t : ℝ, 173 ≤ t → t ≤ 100000 → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t) :
    (43/100) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
      ≤ Work.RHContract.Margin.caC1 ε + Work.RHContract.Margin.caNet2 ε := by
  have h1 := caC1_lower_B ε hε hlo hhi hθ
  have h2 := caNet2_nonneg_B ε hε hlo hhi hθ
  linarith

end Work.RHContract.A.regionII
