import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NPC.Basic

/-- If `N` is a normal `p`-complement of `G` and `K ≤ N` is normal in `G`, then the image of `N`
in `G ⧸ K` is a normal `p`-complement of `G ⧸ K`.  (This is the "quotient by a subgroup of the
complement" step.) -/
theorem hasNormalPComplement_quotient {G : Type*} [Group G] [Finite G] {p : ℕ}
    (K : Subgroup G) [K.Normal] {N : Subgroup G} (h : Work.NPC.IsNormalPComplement p N)
    (hK : K ≤ N) : Work.NPC.HasNormalPComplement p (G ⧸ K) := by
  haveI : N.Normal := h.normal
  refine ⟨N.map (QuotientGroup.mk' K), ?_, ?_, ?_⟩
  · -- the image of a normal subgroup is normal
    exact QuotientGroup.map_normal K N
  · -- the image is a quotient of `N`, so its order divides `|N|`, hence is coprime to `p`
    exact Nat.Coprime.coprime_dvd_left (Subgroup.card_map_dvd N (QuotientGroup.mk' K)) h.coprime_card
  · -- third isomorphism theorem: `(G ⧸ K) ⧸ (N ⧸ K) ≃* G ⧸ N` is a `p`-group
    exact IsPGroup.of_equiv h.isPGroup_quotient
      (QuotientGroup.quotientQuotientEquivQuotient K N hK).symm

end Work.NPC.Basic
