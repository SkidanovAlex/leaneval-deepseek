import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Engine
import Submission.Work.NPC.Frobenius.induction

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

/-- **Frobenius' normal `p`-complement theorem.**  If for every non-identity `p`-subgroup `Q ≤ G`
the quotient `N_G(Q)/C_G(Q)` is a `p`-group, then `G` has a normal `p`-complement.

The proof is the strong induction on `|G|` of `Submission/Work/NPC/Frobenius/induction.lean`
(see `HINTS.md`); it uses that Frobenius' condition is inherited by subgroups and the transfer
kernel `(Q.transferFocal).ker` as the proper normal subgroup with `p`-group quotient.  It does
*not* need the transfer criterion `P ∩ G' = P'`. -/
theorem frobenius_npc {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : Work.NPC.HasFrobeniusCondition p G) : Work.NPC.HasNormalPComplement p G :=
  frobenius_npc_via_induction h

end Work.NPC.Frobenius
