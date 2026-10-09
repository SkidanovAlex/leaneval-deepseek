import Mathlib
import Submission.Work.SSGRoute.gradedStep_diagonal
import Submission.Work.SSGRoute.wordBarDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The graded piece `E(j,j) = ker(Q_{(j+1,1)} → Q_{(j,j)})` as a `G`-set

The kernel of the projection `flowQuotSucc 2 G n j j : Q_{(j+1,1)} → Q_{(j,j)}` is the graded piece
`E(j,j)`; it is stable under the descended action of `G` on `Q_{(j+1,1)}`, and we record the
resulting action as `flowKerSmul`.
-/

noncomputable section

namespace Work.SSGRoute

open Work.CohomologicalShrinking

variable {G : Type*} [Group G] {n : ℕ}

/-- The action of `g : G` on the graded piece `E(j,j) = ker(flowQuotSucc 2 G n j j)`. -/
def flowKerSmul (G : Type*) [Group G] (n j : ℕ) (g : G)
    (c : ↥(flowQuotSucc 2 G n j j).ker) : ↥(flowQuotSucc 2 G n j j).ker :=
  ⟨flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 g
      (c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2), by
    show flowQuotSucc 2 G n j j (g • (c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)) = 1
    rw [flowQuotSucc_smul, c.2, smul_one]⟩

@[simp] theorem flowKerSmul_coe (G : Type*) [Group G] (n j : ℕ) (g : G)
    (c : ↥(flowQuotSucc 2 G n j j).ker) :
    ((flowKerSmul G n j g c : ↥(flowQuotSucc 2 G n j j).ker) :
        flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 g
          (c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) := rfl

end Work.SSGRoute
