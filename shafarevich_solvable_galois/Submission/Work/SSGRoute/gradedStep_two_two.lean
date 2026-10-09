import Mathlib
import Submission.Work.SSGRoute.two_two_graded_pieces
import Submission.Work.SSGRoute.TwoTwoModelDefs
import Submission.Work.SSGRoute.TwoTwoAssembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped commutatorElement

theorem gradedStep_two_two (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : Work.CohomologicalShrinking.flowQuotient 2 G n
        (Work.CohomologicalShrinking.tauSucc 2 2).1
        (Work.CohomologicalShrinking.tauSucc 2 2).2,
      Work.SSGRoute.flowQuotSucc 2 G n 2 2 c = 1 →
      Work.CohomologicalShrinking.flowAction 2 G n
        (Work.CohomologicalShrinking.tauSucc 2 2).1
        (Work.CohomologicalShrinking.tauSucc 2 2).2 δ c = c⁻¹ →
      ∃ e : Work.CohomologicalShrinking.flowQuotient 2 G n
          (Work.CohomologicalShrinking.tauSucc 2 2).1
          (Work.CohomologicalShrinking.tauSucc 2 2).2,
        c = (Work.CohomologicalShrinking.flowAction 2 G n
          (Work.CohomologicalShrinking.tauSucc 2 2).1
          (Work.CohomologicalShrinking.tauSucc 2 2).2 δ e)⁻¹ * e := by
  intro c hc hc2
  exact two_two_graded_step (G := G) (n := n) δ hδ hδ1 c hc hc2

end Work.SSGRoute
