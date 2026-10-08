import Mathlib
import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.FeitSibley.Coherence.scriptSR_deg_Qcomm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.CharQ

/-- `indQH φ` at the identity is `[H : Q] * φ 1`; since `H = Q ⋊ D` the index is `|D|`. -/
theorem indQH_deg {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (φ : ↥h.Q → ℂ) :
    h.indQH φ 1 = (Nat.card h.D : ℂ) * φ 1 := by
  rw [Work.FeitSibley.FSData.indQH, Work.Induction.indFun_apply_one,
      Work.FeitSibley.Coherence.index_subgroupOf_Q h]
  have harg : (⟨((1 : ↥(h.Q.subgroupOf h.H)) : G),
      (1 : ↥(h.Q.subgroupOf h.H)).2⟩ : ↥h.Q) = 1 := Subtype.ext (by simp)
  rw [harg]

end Work.FeitSibley.CharQ
