import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.Coherence.step1
import Submission.Work.FeitSibley.Coherence.step2
import Submission.Work.FeitSibley.Coherence.coherent_union_singleton
import Submission.Work.FeitSibley.Coherence.numeric_step1
import Submission.Work.FeitSibley.Coherence.scriptSR_deg_Qcomm
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_of_le_S
import Submission.Work.FeitSibley.Coherence.SubFSZ_aux
import Submission.Work.FeitSibley.Coherence.X1_coherent
import Submission.Work.FeitSibley.Coherence.X_coherent_of_X1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

theorem coherent_scriptS_sub_FSZ {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hD : h.D ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1)
    (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) :
    Work.Coherence.Coherent (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) (Work.FeitSibley.indLin h.H) := by
  exact X_coherent_of_X1 h hD hp hp2 hpg hab (X1_coherent h hp hp2 hpg hab)

end Work.FeitSibley.Coherence
