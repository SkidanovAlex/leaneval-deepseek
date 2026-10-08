import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.KFP.Transport
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F

set_option linter.style.haveILetI false

namespace Work.CORE4.FpropsAux

open Subgroup

/-- **A `π`-subgroup of a finite nilpotent group lies in `O_π`.**

`N` is nilpotent (a subgroup of the nilpotent `H`), hence is the join of its own Sylow
subgroups (`OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent`).  The image in `H`
of the Sylow `q`-subgroup of `N`, for `q ∈ π`, is a `q`-subgroup of `H`; it is contained in
some Sylow `q`-subgroup `Q` of `H`, which is normal because `H` is nilpotent, and `Q` is a
(normal) `π`-subgroup since `q ∈ π`.  Hence the image lies in `O_π(H)` by the universal
property `Work.CORE4.KFP.le_piCore_of_normal_isPiSubgroup` of the `π`-core. -/
theorem le_piCore_of_isPiSubgroup_of_isNilpotent {H : Type} [Group H] [Finite H]
    [Group.IsNilpotent H] (π : Set ℕ) (N : Subgroup H) (hN : Subgroup.IsPiSubgroup π N) :
    N ≤ Work.GW2.piCore π H := by
  have htop : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← htop, ← OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥N,
    Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpπ : p ∈ π := hN p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  have hpg : IsPGroup p (((default : Sylow p ↥N) : Subgroup ↥N).map N.subtype) :=
    IsPGroup.map (default : Sylow p ↥N).isPGroup' N.subtype
  obtain ⟨Q, hleQ⟩ := hpg.exists_le_sylow
  haveI : (Q : Subgroup H).Normal := OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent Q
  exact hleQ.trans (Work.CORE4.KFP.le_piCore_of_normal_isPiSubgroup (G := H) (π := π)
    (Subgroup.isPiSubgroup_of_isPGroup_of_mem Q.isPGroup' hpπ))

/-- **A `π`-subgroup of a nilpotent subgroup `F ≤ G` lies in `O_π(F)`.**

The subgroup `N` corresponds to `N.subgroupOf F ≤ F` (same cardinality, because `N ≤ F`), a
`π`-subgroup of the group `↥F`, and `le_piCore_of_isPiSubgroup_of_isNilpotent` applies inside
`↥F`. -/
theorem le_map_piCore_of_isPiSubgroup_of_isNilpotent {G : Type} [Group G] [Finite G]
    (F : Subgroup G) [Group.IsNilpotent ↥F] (π : Set ℕ) {N : Subgroup G} (hNF : N ≤ F)
    (hN : Subgroup.IsPiSubgroup π N) : N ≤ (Work.GW2.piCore π F).map F.subtype := by
  have hmap : (N.subgroupOf F).map F.subtype = N :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hNF)
  have hcard : Nat.card ↥(N.subgroupOf F) = Nat.card ↥N := by
    rw [← Subgroup.card_map_of_injective F.subtype_injective, hmap]
  have hNpi : Subgroup.IsPiSubgroup π (N.subgroupOf F) := fun p hp => hN p (hcard ▸ hp)
  intro x hx
  have hxF : (⟨x, hNF hx⟩ : ↥F) ∈ N.subgroupOf F := Subgroup.mem_subgroupOf.mpr hx
  have hxpi : (⟨x, hNF hx⟩ : ↥F) ∈ Work.GW2.piCore π F :=
    le_piCore_of_isPiSubgroup_of_isNilpotent (H := ↥F) π (N.subgroupOf F) hNpi hxF
  exact ⟨⟨x, hNF hx⟩, hxpi, rfl⟩

end Work.CORE4.FpropsAux
