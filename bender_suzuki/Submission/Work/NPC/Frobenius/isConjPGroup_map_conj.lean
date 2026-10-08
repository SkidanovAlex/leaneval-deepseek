/-
Area A9 of the Feit--Thompson drive: Frobenius' hypothesis.

`IsConjPGroup p Q` (the quotient `N_G(Q)/C_G(Q)` is a `p`-group) is invariant under
conjugation of the subgroup `Q`: passing to a conjugate subgroup just conjugates the
normalizer and the centralizer, which does not change the isomorphism type of
`N_G(Q)/C_G(Q)`.

This is the special case `e = MulAut.conj g` of `isConjPGroup_map_equiv`, which is proved
in `Submission/Work/NPC/Frobenius/hasFrobeniusCondition_iff_forall_le_sylow.lean`.
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_iff_forall_le_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

/-- `IsConjPGroup` is invariant under conjugation of the subgroup: the isomorphism
`MulAut.conj g : G ≃* G` induces an isomorphism `N_G(Q)/C_G(Q) ≃* N_G(gQg⁻¹)/C_G(gQg⁻¹)`. -/
theorem isConjPGroup_map_conj {G : Type*} [Group G] {p : ℕ} (Q : Subgroup G) (g : G) :
    Work.NPC.IsConjPGroup p (Q.map (MulAut.conj g).toMonoidHom) ↔ Work.NPC.IsConjPGroup p Q :=
  isConjPGroup_map_equiv (MulAut.conj g) Q

end Work.NPC.Frobenius
