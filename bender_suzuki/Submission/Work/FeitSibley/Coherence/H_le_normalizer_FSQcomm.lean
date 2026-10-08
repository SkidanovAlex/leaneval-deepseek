import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

/-- `H` normalises the commutator subgroup `Q' = [Q,Q]` of the T.I. subgroup `Q`: indeed `Q` is
normal in `H`, and the commutator subgroup is taken to itself by every automorphism that fixes
`Q`. -/
theorem H_le_normalizer_FSQcomm {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    h.H ≤ Subgroup.normalizer (Work.FeitSibley.Coherence.FSQcomm h : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [FSQcomm]
  rw [Subgroup.map_commutator]
  have hgQ : g ∈ Subgroup.normalizer (h.Q : Set G) := h.Q_normal_in_H hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hgQ
  rw [hgQ]

end Work.FeitSibley.Coherence
