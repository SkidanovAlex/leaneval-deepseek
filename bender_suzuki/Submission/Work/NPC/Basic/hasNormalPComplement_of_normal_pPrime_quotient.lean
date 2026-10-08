import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Basic

/-- If `N ⊴ G` has order coprime to `p`, and the quotient `G ⧸ N` has a normal `p`-complement,
then so does `G`: the preimage of the complement of `G ⧸ N` under the quotient map is normal
in `G`, has order coprime to `p` (it is an extension of `N` by a group of order coprime to `p`),
and the quotient of `G` by it is isomorphic to the quotient of `G ⧸ N` by its complement. -/
theorem hasNormalPComplement_of_normal_pPrime_quotient {G : Type*} [Group G] [Finite G]
    {p : ℕ} {N : Subgroup G} [N.Normal] (hN : (Nat.card N).Coprime p)
    (h : Work.NPC.HasNormalPComplement p (G ⧸ N)) : Work.NPC.HasNormalPComplement p G := by
  obtain ⟨Mbar, hMbar⟩ := h
  -- `Mbar ⊴ G ⧸ N` is the normal `p`-complement of the quotient.
  letI : Mbar.Normal := hMbar.normal
  -- its preimage in `G` under the quotient map will be the normal `p`-complement of `G`.
  let M : Subgroup G := Mbar.comap (QuotientGroup.mk' N)
  have hNM : N ≤ M := by
    intro x hx
    show QuotientGroup.mk' N x ∈ Mbar
    have hx' : QuotientGroup.mk' N x = 1 := by simpa using hx
    rw [hx']; exact Mbar.one_mem
  -- the preimage of `Mbar` is exactly `Mbar`
  have hmap : Subgroup.map (QuotientGroup.mk' N) M = Mbar := by
    show Subgroup.map (QuotientGroup.mk' N) (Mbar.comap (QuotientGroup.mk' N)) = Mbar
    rw [Subgroup.map_comap_eq]
    have hrange : (QuotientGroup.mk' N).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
    rw [hrange, top_inf_eq]
  -- counting: `M` is an extension of `N` by `Mbar`, hence `|M| = |N| * |Mbar|`
  have hcard : Nat.card M = Nat.card N * Nat.card Mbar := by
    have h1 := QuotientGroup.card_preimage_mk N (Mbar : Set (G ⧸ N))
    exact h1
  haveI : M.Normal := Subgroup.normal_comap (QuotientGroup.mk' N)
  -- `G ⧸ M` is the quotient of `G ⧸ N` by `Mbar`
  have hiso : (G ⧸ N) ⧸ Mbar ≃* G ⧸ M :=
    (QuotientGroup.quotientMulEquivOfEq hmap).symm.trans
      (QuotientGroup.quotientQuotientEquivQuotient N M hNM)
  refine ⟨M, Subgroup.normal_comap (QuotientGroup.mk' N), ?_, ?_⟩
  · rw [hcard]; exact hN.mul_left hMbar.coprime_card
  · exact hMbar.isPGroup_quotient.of_equiv hiso

end Work.NPC.Basic
