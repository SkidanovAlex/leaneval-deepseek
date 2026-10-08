import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Basic.isNormalPComplement_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NPC.Frobenius

/-- The property of being a normal `p`-complement is invariant under automorphisms: if `N` is a
normal `p`-complement of `G` and `e : G ≃* G` is an automorphism, then so is `N.map e` (the
quotient `G ⧸ N.map e ≃* G ⧸ N` stays a `p`-group and the order of `N.map e` is `Nat.card N`). -/
theorem isNormalPComplement_map_mulEquiv {G : Type*} [Group G] {p : ℕ} {N : Subgroup G}
    (h : Work.NPC.IsNormalPComplement p N) (e : G ≃* G) :
    Work.NPC.IsNormalPComplement p (N.map (e : G →* G)) := by
  haveI hnorm : (N.map (e : G →* G)).Normal := h.normal.map (e : G →* G) e.surjective
  haveI : N.Normal := h.normal
  refine ⟨hnorm, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact h.coprime_card
  · exact h.isPGroup_quotient.of_equiv (QuotientGroup.congr N (N.map (e : G →* G)) e rfl)

/-- **Lifting a normal `p`-complement along a `p`-group quotient.**

If `H ⊴ G` is normal with `G ⧸ H` a `p`-group, and `H` has a normal `p`-complement, then so does
`G`.  Indeed, the normal `p`-complement `N` of `H` is unique, hence fixed by every automorphism of
`H`, i.e. characteristic in `H`; since `H ⊴ G`, the image `N.map H.subtype` is normal in `G`
(`Subgroup.normal_of_characteristic_of_normal`).  Its order is `|N|`, coprime to `p`, and
`G ⧸ N.map H.subtype` is a `p`-group because it is an extension of the `p`-group
`H ⧸ N ≅ (H ⧸ N)` by the `p`-group `G ⧸ H` (argued elementwise below). -/
theorem hasNormalPComplement_of_normal_pGroup_quotient {G : Type*} [Group G] [Finite G]
    {p : ℕ} {H : Subgroup G} [H.Normal] (hquot : IsPGroup p (G ⧸ H))
    (hH : Work.NPC.HasNormalPComplement p ↥H) : Work.NPC.HasNormalPComplement p G := by
  obtain ⟨N, hN⟩ := hH
  haveI : Finite ↥H := inferInstance
  haveI hNnorm : N.Normal := hN.normal
  -- `N` is the unique normal `p`-complement of `H`, hence characteristic in `H`.
  haveI hNchar : N.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    exact (Work.NPC.Basic.isNormalPComplement_unique hN
      (isNormalPComplement_map_mulEquiv hN φ)).symm
  -- a characteristic subgroup of a normal subgroup is normal in the ambient group.
  haveI hN'norm : (N.map H.subtype).Normal := inferInstance
  refine ⟨N.map H.subtype, hN'norm, ?_, ?_⟩
  · -- the order of `N.map H.subtype` is `|N|`, which is coprime to `p`.
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hN.coprime_card
  · -- `G ⧸ N.map H.subtype` is a `p`-group.
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N.map H.subtype) x
    obtain ⟨k, hk⟩ := hquot (QuotientGroup.mk' H g)
    -- `g ^ p ^ k ∈ H`, so it defines an element `h` of `H`.
    have hgk : g ^ p ^ k ∈ H := by
      have h2 : QuotientGroup.mk' H (g ^ p ^ k) = 1 := by rw [map_pow]; exact hk
      exact (QuotientGroup.eq_one_iff (g ^ p ^ k)).mp h2
    set h : ↥H := ⟨g ^ p ^ k, hgk⟩ with hh_def
    -- in the `p`-group `H ⧸ N` the class of `h` has `p`-power order, so `h ^ p ^ m ∈ N`.
    obtain ⟨m, hm⟩ := hN.isPGroup_quotient (QuotientGroup.mk' N h)
    have hhm : h ^ p ^ m ∈ N := by
      have h3 : QuotientGroup.mk' N (h ^ p ^ m) = 1 := by rw [map_pow]; exact hm
      exact (QuotientGroup.eq_one_iff (h ^ p ^ m)).mp h3
    -- the image of `h ^ p ^ m` in `G` is `g ^ p ^ (k + m)`.
    have himg : H.subtype (h ^ p ^ m) = g ^ p ^ (k + m) := by
      rw [map_pow]
      change (g ^ p ^ k) ^ p ^ m = g ^ p ^ (k + m)
      rw [← pow_mul, ← pow_add]
    have hmem : g ^ p ^ (k + m) ∈ N.map H.subtype := by
      rw [← himg]
      exact Subgroup.mem_map_of_mem H.subtype hhm
    exact ⟨k + m, by rw [← map_pow]; exact (QuotientGroup.eq_one_iff (g ^ p ^ (k + m))).mpr hmem⟩

end Work.NPC.Frobenius
