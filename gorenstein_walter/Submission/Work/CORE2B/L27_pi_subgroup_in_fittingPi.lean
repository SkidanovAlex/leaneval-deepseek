import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.L27_fittingPi_compl_of_odd

namespace Work.CORE2B

/-- General form of Bender 1981, Lemma 2.7 (a): any `π`-subgroup `N` of a finite group `G` that is
contained in `F(M)` lies in `F_π(M) = O_π(F(M))`.

The `π`-subgroup `N ≤ F(M) ≤ M` corresponds, inside `↥M`, to `N.subgroupOf M ≤ F(M)`, a
`π`-subgroup of the nilpotent group `F(M)` with the same cardinality; it therefore lies in
`O_π(F(M))` (`le_map_piCore_of_isPiSubgroup`), which after unfolding the two `…In` subgroups is
exactly the claim. -/
theorem L27_pi_subgroup_in_fittingPi {G : Type} [Group G] [Finite G]
    (M N : Subgroup G) (π : Set ℕ) (hN : N ≤ Work.GW2.fittingIn M)
    (hNpi : Subgroup.IsPiSubgroup π N) : N ≤ Work.GW2.fittingPiIn π M := by
  -- `N ⊆ F(M) ⊆ M` as subsets of `G`
  have hNM : N ≤ M := hN.trans (Subgroup.map_subtype_le _)
  -- the same subgroup, viewed inside `↥M`, and its containment in `F(M)`
  have hNF : N.subgroupOf M ≤ Work.GW2.fitting ↥M := by
    intro x hx
    have hx' : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hN hx')
    exact Subtype.ext hyx ▸ hy
  -- it has the same cardinality as `N`
  have hcard : Nat.card ↥(N.subgroupOf M) = Nat.card N := by
    have hmap : (N.subgroupOf M).map M.subtype = N :=
      Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hNM)
    rw [← Subgroup.card_map_of_injective M.subtype_injective, hmap]
  -- so it is a `π`-subgroup, and lies in `F_π(M)` by section 3 of `L27_fittingPi_compl_of_odd`
  have hpi : Subgroup.IsPiSubgroup π (N.subgroupOf M) := fun p hp => hNpi p (hcard ▸ hp)
  have hstep : N.subgroupOf M ≤ Work.GW2.fittingPi π M :=
    le_map_piCore_of_isPiSubgroup (Work.GW2.fitting ↥M) π hNF hpi
  -- transport back into `G`
  intro x hx
  have hxM : x ∈ M := hNM hx
  have hxN : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
  obtain ⟨z, hz, hzF⟩ := Subgroup.mem_map.mp (hstep hxN)
  refine Subgroup.mem_map.mpr ⟨(Work.GW2.fitting ↥M).subtype z, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  · exact congrArg Subtype.val hzF

end Work.CORE2B
