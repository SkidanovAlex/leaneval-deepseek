import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.GTest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

theorem HkIntegrand_gTest_expand (p : ℝ) (ε z θ : ℝ) :
    Work.Spaces.HkIntegrand p 2 (gTest ε) z θ
      = (gTest ε z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + (ε * gPhiD1 z * gPsi θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + (ε * gPhiD2 z * gPsi θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + (ε * gPhi z * gPsiD1 θ * Work.Spaces.Wt p z θ) ^ 2
        + (ε * gPhiD1 z * gPsiD1 θ * Work.Spaces.Wt p z θ) ^ 2
        + (ε * gPhi z * gPsiD2 θ * Work.Spaces.Wt p z θ) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.reduceAdd, Nat.reduceLeDiff, and_true, and_false, ite_true, ite_false,
    zero_add, add_zero, Work.Spaces.DzIter_zero, DzIter_one_gTest, DzIter_two_gTest,
    mixed_zero_one_gTest, mixed_one_one_gTest, mixed_zero_two_gTest, gTest_apply]
  ring

end Work.R1G
