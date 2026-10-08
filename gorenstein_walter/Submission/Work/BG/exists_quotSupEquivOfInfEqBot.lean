import Mathlib
import Submission.Work.BG.Defs

namespace Work.BG

theorem exists_quotSupEquivOfInfEqBot {G : Type} [Group G] (H N : Subgroup G)
    [hN : (N.subgroupOf (H ⊔ N)).Normal] (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hinf : H ⊓ N = ⊥) : Nonempty (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N) ≃* ↥H) := by
  -- `N` is normal in `H` because `H` normalizes `N`.
  haveI : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  -- Since `H ⊓ N = ⊥`, the subgroup `N` meets `H` trivially, so `N.subgroupOf H = ⊥`.
  have hsub : N.subgroupOf H = ⊥ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hx
      have hmem : (x : G) ∈ H ⊓ N := ⟨x.2, hx⟩
      rw [hinf] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    · intro hx
      rw [hx]
      exact N.one_mem
  -- Noether's second isomorphism theorem `H/(H∩N) ≃* (HN)/N`, composed with `H/⊥ ≃* H`.
  refine ⟨(QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot)⟩

end Work.BG
