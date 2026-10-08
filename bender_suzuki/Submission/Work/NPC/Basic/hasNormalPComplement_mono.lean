import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NPC.Basic

/-- **Monotonicity of having a normal `p`-complement**:  if `G` has a normal `p`-complement then
so does every subgroup `H ≤ G`.

Indeed if `N` is a normal `p`-complement of `G`, then `N ∩ H` (realised inside `H` as
`N.subgroupOf H`) is a normal `p`-complement of `H`:
* it is normal in `H` because `N` is normal in `G` (a preimage of a normal subgroup);
* its order divides `|N|`, hence is coprime to `p`;
* `H ⧸ (N ∩ H)` embeds into the `p`-group `G ⧸ N` via the composite `H → G → G ⧸ N`, whose
  kernel is exactly `N ∩ H`, so it is a `p`-group. -/
theorem hasNormalPComplement_mono {G : Type*} [Group G] [Finite G] {p : ℕ}
    (H : Subgroup G) (h : Work.NPC.HasNormalPComplement p G) :
    Work.NPC.HasNormalPComplement p H := by
  obtain ⟨N, hN⟩ := h
  haveI : N.Normal := hN.normal
  -- `N ∩ H` viewed as a subgroup of `H`, together with (an instance of) its normality.
  haveI hK : (N.subgroupOf H).Normal := hN.normal.comap H.subtype
  -- The composite `H → G → G ⧸ N` has kernel `N ∩ H`.
  let φ : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hker : φ.ker = N.subgroupOf H := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  refine ⟨N.subgroupOf H, hK, ?_, ?_⟩
  · -- `|N ∩ H| ∣ |N|`, and `|N|` is coprime to `p`.
    exact hN.coprime_card.coprime_dvd_left
      (Subgroup.card_comap_dvd_of_injective N H.subtype H.subtype_injective)
  · -- `H ⧸ (N ∩ H) ≅ φ.range ≤ G ⧸ N`, a `p`-group.
    have hrange : IsPGroup p φ.range := hN.isPGroup_quotient.to_subgroup φ.range
    exact IsPGroup.of_equiv hrange
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange φ)).symm

end Work.NPC.Basic
