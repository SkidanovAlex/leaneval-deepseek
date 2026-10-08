import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_of_hasNormalPComplement
import Submission.Work.NPC.Frobenius.hasNormalPComplement_of_conjugacyClosed_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

theorem hasFrobeniusCondition_of_conjugacyClosed_sylow {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (h : ∀ x y : ↥(P : Subgroup G), IsConj (x : G) (y : G) → IsConj x y) :
    Work.NPC.HasFrobeniusCondition p G :=
  hasFrobeniusCondition_of_hasNormalPComplement
    (hasNormalPComplement_of_conjugacyClosed_sylow P h)

end Work.NPC.Frobenius
