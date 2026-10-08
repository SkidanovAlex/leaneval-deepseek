import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NPC.Basic

/-- If `f : G →* H` is a surjective homomorphism of finite groups and `G` has a normal
`p`-complement, then so does `H`: the image of a normal `p`-complement is again one, since
`|f(N)|` divides `|N|` (so is coprime to `p`) and `H ⧸ f(N)` is a quotient of `G ⧸ N`
(so is a `p`-group). -/
theorem hasNormalPComplement_of_surjective {G : Type*} [Group G] [Finite G] {H : Type*} [Group H]
    [Finite H] {p : ℕ} (f : G →* H) (hf : Function.Surjective f)
    (h : Work.NPC.HasNormalPComplement p G) : Work.NPC.HasNormalPComplement p H := by
  obtain ⟨N, hN⟩ := h
  haveI hNnorm : N.Normal := hN.normal
  haveI hMnorm : (N.map f).Normal := hN.normal.map f hf
  refine ⟨N.map f, hN.normal.map f hf, ?_, ?_⟩
  · -- `|f(N)|` divides `|N|`, which is coprime to `p`
    exact Nat.Coprime.coprime_dvd_left (Subgroup.card_map_dvd N f) hN.coprime_card
  · -- `H ⧸ f(N)` is a quotient of the `p`-group `G ⧸ N`
    have hle : N ≤ (N.map f).comap f := Subgroup.le_comap_map f N
    refine IsPGroup.of_surjective hN.isPGroup_quotient
      (QuotientGroup.map N (N.map f) f hle) ?_
    exact QuotientGroup.map_surjective_of_surjective N (N.map f) f
      (QuotientGroup.mk_surjective.comp hf) hle

end Work.NPC.Basic
