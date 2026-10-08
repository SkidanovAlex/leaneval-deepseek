import Mathlib
import Submission.Work.RED.Basic

namespace Work.RED

theorem MNF_char_free (G : Type*) [Group G] [Finite G] (N : Subgroup G)
    (hN : Work.RED.GW2.IsMinimalNormal N) (H : Subgroup G) (hHle : H ≤ N)
    (hHchar : (H.subgroupOf N).Characteristic) : H = ⊥ ∨ H = N := by
  -- `N` is normal in `G`, so `G` acts on `N` by conjugation.
  haveI hN_normal : N.Normal := Work.RED.GW2.IsMinimalNormal.normal hN
  -- A characteristic subgroup of a normal subgroup is normal in the ambient group.
  haveI : (H.subgroupOf N).Characteristic := hHchar
  have hnorm : ((H.subgroupOf N).map N.subtype).Normal := inferInstance
  -- `H ≤ N`, so the transport of `H.subgroupOf N` back into `G` is `H` itself.
  rw [Subgroup.map_subgroupOf_eq_of_le hHle] at hnorm
  -- Minimality of `N` now pins `H` down.
  rcases eq_or_ne H ⊥ with h | h
  · exact Or.inl h
  · exact Or.inr (Work.RED.GW2.IsMinimalNormal.eq_of_le hN hnorm h hHle)

end Work.RED
