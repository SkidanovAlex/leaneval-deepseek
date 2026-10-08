import Mathlib
import Submission.Work.RED.Basic

/-!
# Quotienting by the odd core preserves `DihOrCycSylow` (`Work.RED.GW2.RedFacts.quotSylow`)

If every Sylow 2-subgroup of `G` is cyclic or dihedral, then the same holds for
`G ⧸ O(G)`, where `O(G) = O_{2'}(G)` has odd order.

The two ingredients are:

* a Sylow 2-subgroup `P` of `G` meets the odd-order subgroup `O(G)` trivially
  (`P ⊓ O(G) = ⊥`), because the order of the intersection divides both the odd number
  `|O(G)|` and the 2-power `|P|`;
* consequently the quotient map is injective on `P`, so `P ≃* P·O(G)/O(G)`.

Hence the images of the Sylow 2-subgroups of `G` are Sylow 2-subgroups of `G ⧸ O(G)`
(`Sylow.mapSurjective`), and being cyclic or dihedral transfers along the isomorphism.
Since by Sylow's theorem (`Sylow.equiv`) *every* Sylow 2-subgroup of the quotient is
isomorphic to such an image, the result follows.
-/

namespace Work.RED

namespace QuotientSylowAux

open Subgroup

/-- A Sylow `2`-subgroup `P` of a finite group `G` meets an odd-order subgroup `O` trivially:
`|P ⊓ O|` divides both the 2-power `|P|` and the odd number `|O|`, hence equals `1`. -/
theorem sylow_inf_eq_bot {G : Type} [Group G] [Finite G] (P : Sylow 2 G)
    (O : Subgroup G) (hodd : Odd (Nat.card O)) : (P : Subgroup G) ⊓ O = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (P.isPGroup' : IsPGroup 2 ↥(P : Subgroup G))
  have hk : Odd (Nat.card ↥((P : Subgroup G) ⊓ O)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_right)
  have hcop : Nat.Coprime (Nat.card ↥((P : Subgroup G) ⊓ O)) (2 ^ n) :=
    (Nat.coprime_two_right.mpr hk).pow_right n
  have hdvd : Nat.card ↥((P : Subgroup G) ⊓ O) ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact Subgroup.card_eq_one.mp (hcop.eq_one_of_dvd hdvd)

/-- If `P ⊓ O = ⊥`, the quotient map `G →* G ⧸ O` is injective on `P`, so `P` is
isomorphic to its image. -/
theorem mulEquiv_map_quotientMk {G : Type} [Group G] (P : Sylow 2 G) (O : Subgroup G)
    [O.Normal] (hker : (P : Subgroup G) ⊓ O = ⊥) :
    Nonempty (↥(P : Subgroup G) ≃* ↥((P : Subgroup G).map (QuotientGroup.mk' O))) := by
  have hmem : ∀ x : ↥(P : Subgroup G),
      ((QuotientGroup.mk' O).comp (P : Subgroup G).subtype) x ∈
        (P : Subgroup G).map (QuotientGroup.mk' O) :=
    fun x => ⟨x, x.2, rfl⟩
  refine ⟨MulEquiv.ofBijective
    (MonoidHom.codRestrict ((QuotientGroup.mk' O).comp (P : Subgroup G).subtype) _ hmem)
    ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have h1 : QuotientGroup.mk' O x = QuotientGroup.mk' O y := by
      have hh := congrArg
        (fun z : ↥((P : Subgroup G).map (QuotientGroup.mk' O)) => (z : G ⧸ O)) hxy
      rw [MonoidHom.codRestrict_apply, MonoidHom.codRestrict_apply] at hh
      simpa using hh
    have h2 : QuotientGroup.mk' O (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 : x * y⁻¹ ∈ O := by
      rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
      exact h2
    have h4 : x * y⁻¹ ∈ (P : Subgroup G) := mul_mem hx (inv_mem hy)
    have h5 : x * y⁻¹ = 1 := by
      have h6 : x * y⁻¹ ∈ (⊥ : Subgroup G) := by rw [← hker]; exact ⟨h4, h3⟩
      simpa using h6
    exact Subtype.ext (mul_inv_eq_one.mp h5)
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, hpy⟩ := hy
    refine ⟨⟨p, hp⟩, Subtype.ext ?_⟩
    rw [MonoidHom.codRestrict_apply]
    simpa using hpy

end QuotientSylowAux

theorem QuotientSylowDihedral {G : Type} [Group G] [Finite G]
    (hoddO : Odd (Nat.card (Work.RED.GW2.oddCore G))) (h : Work.RED.GW2.DihOrCycSylow G) :
    Work.RED.GW2.DihOrCycSylow (G ⧸ Work.RED.GW2.oddCore G) := by
  intro Q
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 G))
  -- `P` meets `O(G)` trivially, so it embeds into the quotient
  have hker : (P : Subgroup G) ⊓ Work.RED.GW2.oddCore G = ⊥ :=
    QuotientSylowAux.sylow_inf_eq_bot P _ hoddO
  have hPmIso : Nonempty (↥(P : Subgroup G) ≃*
      ↥((P.mapSurjective (QuotientGroup.mk'_surjective (Work.RED.GW2.oddCore G)) :
        Sylow 2 (G ⧸ Work.RED.GW2.oddCore G)) : Subgroup (G ⧸ Work.RED.GW2.oddCore G))) := by
    obtain ⟨e⟩ := QuotientSylowAux.mulEquiv_map_quotientMk P (Work.RED.GW2.oddCore G) hker
    refine ⟨e.trans (MulEquiv.subgroupCongr ?_).symm⟩
    exact Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (Work.RED.GW2.oddCore G)) P
  rcases h P with hcyc | ⟨n, hn⟩
  · -- the image of a cyclic Sylow 2-subgroup is cyclic
    left
    obtain ⟨e⟩ := hPmIso
    have hcyc2 : IsCyclic ↥((P.mapSurjective (QuotientGroup.mk'_surjective
        (Work.RED.GW2.oddCore G)) : Sylow 2 (G ⧸ Work.RED.GW2.oddCore G)) :
        Subgroup (G ⧸ Work.RED.GW2.oddCore G)) := (MulEquiv.isCyclic e).mp hcyc
    exact (MulEquiv.isCyclic (Sylow.equiv _ Q)).mp hcyc2
  · -- the image of a dihedral Sylow 2-subgroup is dihedral
    right
    obtain ⟨e⟩ := hn
    obtain ⟨e'⟩ := hPmIso
    exact ⟨n, ⟨(Sylow.equiv _ Q).symm.trans (e'.symm.trans e)⟩⟩

end Work.RED
