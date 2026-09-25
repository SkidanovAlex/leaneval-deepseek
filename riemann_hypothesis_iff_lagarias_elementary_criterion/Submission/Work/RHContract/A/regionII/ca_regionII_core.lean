import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.regionII.theta_deficit_bound
import Submission.Work.RHContract.A.regionII.caC1_add_caNet2_lower_A
import Submission.Work.RHContract.A.regionII.caC1_add_caNet2_lower_B
import Submission.Work.RHContract.A.regionII.caW_upper_A
import Submission.Work.RHContract.A.regionII.caW_upper_B
import Submission.Work.RHContract.A.regionII.caK3_upper_A
import Submission.Work.RHContract.A.regionII.caK3_upper_B
import Submission.Work.RHContract.A.regionII.caPsiTail_bound_A
import Submission.Work.RHContract.A.regionII.caPsiTail_bound_B
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.psiTail_ge_of_RH
import Submission.Work.RHContract.A.psi_sub_le_of_RH

/-!
# Region II of AREA A: Robin's inequality at CA numbers with `30000 ≤ ξ(ε) < 10^8`

The assembly of `Submission/Work/RHContract/A/regionII/*`:

* `ca_margin_lower` (Lemma M) reduces `γ + logloglog N − log(σ N / N) ≥ 0` to
  `psiTail ξ + caC1 ε + caNet2 ε − caW ε − caK3 ε ≥ 0`;
* on each half `[30000,10^5)` / `[10^5,10^8)` the five terms are bounded:
  `psiTail ≥ −(J)·caU`, `caC1 + caNet2 ≥ (C)·caU`, `caW ≤ W·caU`, `caK3 ≤ K·caU`,
  with `C > J + W + K` (the specific lemmas are named in the proof below).
-/

namespace Work.RHContract.A.regionII

theorem ca_regionII_core (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε)
    (hlo : 30000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < (10 : ℝ) ^ 8) :
    0 ≤ Real.eulerMascheroniConstant
        + Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)))
        - Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
            / ((Work.RHPlan.caNumber ε : ℕ) : ℝ)) := by
  have hξ1530 : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by linarith
  have hmarg := Work.RHContract.A.ca_margin_lower ε hε hξ1530
  have hθ : ∀ t : ℝ, 173 ≤ t → t ≤ 100000 → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t :=
    fun t h1 h2 => theta_deficit_bound t h1 h2
  have hξ1 : (1 : ℝ) < (Work.RHPlan.caXi ε : ℝ) := by linarith
  have hu : 0 < Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) := by
    rw [Work.RHContract.A.RegionII.caU]
    exact one_div_pos.mpr (mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos hξ1))
  have hkey : (0 : ℝ) ≤ Work.RHContract.psiTail (Work.RHPlan.caXi ε : ℝ)
      + Work.RHContract.Margin.caC1 ε + Work.RHContract.Margin.caNet2 ε
      - Work.RHContract.Margin.caW ε - Work.RHContract.Margin.caK3 ε := by
    rcases lt_or_ge ((Work.RHPlan.caXi ε : ℝ)) 100000 with hlt | hge
    · have hJ := caPsiTail_bound_A h ε hε hlo hlt
      have hCN := caC1_add_caNet2_lower_A ε hε hlo hlt hθ
      have hW := caW_upper_A ε hε hlo hlt hθ
      have hK := caK3_upper_A ε hε hlo hlt
      have hpos : (0 : ℝ) < (3 / 1000) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) :=
        mul_pos (by norm_num) hu
      linarith
    · have hA2 : |Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) - (Work.RHPlan.caXi ε : ℝ)|
          ≤ 0.45 * (Work.RHPlan.caXi ε : ℝ) ^ (3 / 4 : ℝ) + 2 :=
        Work.RHContract.A.psi_sub_le_of_RH h _ (by linarith)
      have hJ := caPsiTail_bound_B h ε hε hge hhi
      have hCN := caC1_add_caNet2_lower_B ε hε hge hhi hθ
      have hW := caW_upper_B ε hε hge hhi hA2
      have hK := caK3_upper_B ε hε hge hhi hA2
      have hpos : (0 : ℝ) < (6 / 1000) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) :=
        mul_pos (by norm_num) hu
      linarith
  linarith

end Work.RHContract.A.regionII
