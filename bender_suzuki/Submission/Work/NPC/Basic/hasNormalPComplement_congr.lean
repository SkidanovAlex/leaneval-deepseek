import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NPC.Basic

/-- `IsPGroup` is invariant under isomorphism of groups. -/
theorem isPGroup_of_mulEquiv {p : ℕ} {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : IsPGroup p A) : IsPGroup p B := by
  intro b
  obtain ⟨k, hk⟩ := h (e.symm b)
  exact ⟨k, by simpa using congrArg (⇑e) hk⟩

/-- Having a normal `p`-complement is invariant under isomorphism of finite groups. -/
theorem hasNormalPComplement_congr {G : Type*} [Group G] [Finite G] {H : Type*} [Group H]
    [Finite H] {p : ℕ} (e : G ≃* H) (h : Work.NPC.HasNormalPComplement p G) :
    Work.NPC.HasNormalPComplement p H := by
  obtain ⟨N, hN⟩ := h
  haveI hNn : N.Normal := hN.normal
  have hmap : (N.map (e : G →* H)).Normal := hNn.map (e : G →* H) e.surjective
  haveI hmapI : (N.map (e : G →* H)).Normal := hmap
  refine ⟨N.map (e : G →* H), hmap, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hN.coprime_card
  · exact isPGroup_of_mulEquiv (QuotientGroup.congr N (N.map (e : G →* H)) e rfl)
      hN.isPGroup_quotient

end Work.NPC.Basic
