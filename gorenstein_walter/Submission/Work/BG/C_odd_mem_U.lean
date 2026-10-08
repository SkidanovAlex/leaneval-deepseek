import Mathlib
import Submission.Work.BG.invJCard
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.S_le_H

/-!
# Area BG: an odd-order element centralizing `S` lies in `U = O(C_G(t))`

`Work.BG.C_odd_mem_U`: if `c` centralizes the dihedral Sylow `2`-subgroup `D.S` and has odd
order, then `c ∈ D.U = O_{2'}(C_G(D.t))` (transported into `G`).

The mathematics is two steps, both available in the workspace:

* `D.t` is central in `D.S` (`Work.BG.S_le_H`), so any element centralizing `D.S` lies in
  `D.H = C_G(D.t)`;
* `C_G(t) = O(C_G(t)) · S` (`Work.GW2.CentralizerSplitProp`, proved in
  `Submission/Work/BG/splitglue/Split.lean`), and in a group that is the product of a normal
  odd subgroup `U` with a `2`-group `S`, every odd-order subgroup lies in `U` (the index
  computation below, `le_of_sup_isPGroup`, is reproduced here because the CORE2A module
  holding it imports `Submission.Work.ASM.Defs`, whose `Work.GW2.BenderSetup` clashes with the
  copy in `Submission.Work.GLUE.Defs` already pulled in by the split-gluing file).

Consequently the odd-order subgroup `⟨c⟩ ≤ D.H` satisfies `⟨c⟩ ≤ D.U`, whence `c ∈ D.U`.
-/

namespace Work.BG

open Subgroup

/-- **Index computation.** If `U` is a normal subgroup of a finite group `G` with `U ⊔ S = ⊤`
for a `2`-group `S`, then every subgroup `X` of odd order lies in `U`: the relative index
`U.relIndex X` divides both `|X|` (odd) and `|S|` (a power of two), hence is `1`. -/
private theorem le_of_sup_isPGroup {G : Type*} [Group G] [Finite G] {U S X : Subgroup G}
    [U.Normal] (hUS : U ⊔ S = ⊤) (hS : IsPGroup 2 S) (hX : Odd (Nat.card X)) : X ≤ U := by
  have h1 : U.relIndex X ∣ U.index := Subgroup.relIndex_dvd_index_of_normal U X
  have hidx : U.index = U.relIndex S := by
    rw [← Subgroup.relIndex_top_right, ← hUS, Subgroup.relIndex_sup_left]
  have h2 : U.relIndex X ∣ U.relIndex S := hidx ▸ h1
  have h3 : U.relIndex X ∣ Nat.card S := h2.trans (Subgroup.relIndex_dvd_card U S)
  have h4 : U.relIndex X ∣ Nat.card X := Subgroup.relIndex_dvd_card U X
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hS
  have h5 : U.relIndex X ∣ 2 ^ n := hn ▸ h3
  have hnot : ¬ 2 ∣ Nat.card X := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hX
  have hcop : Nat.Coprime (2 ^ n) (Nat.card X) :=
    (Nat.prime_two.coprime_pow_of_not_dvd (m := n) hnot).symm
  have hone : U.relIndex X = 1 := Nat.eq_one_of_dvd_coprimes hcop h5 h4
  exact Subgroup.relIndex_eq_one.mp hone

/-- **Odd-order subgroups live in `O_{2'}` when the complement is a `2`-group.** If
`U = O_{2'}(H)` (the largest normal odd-order subgroup of `H`, transported into `G`) and
`H = U ⊔ S` with `S` a `2`-group, then every odd-order subgroup of `H` lies in `U`. -/
private theorem odd_subgroup_le_oddCoreIn {G : Type*} [Group G] [Finite G] (H S : Subgroup G)
    (hUS : Work.GW2.oddCoreIn H ⊔ S = H) (hS : IsPGroup 2 S) :
    ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → X ≤ Work.GW2.oddCoreIn H := by
  intro X hXH hXodd
  -- `U ≤ H` (as the image of `O_{2'}(H)` under `H.subtype`) and `S ≤ H`.
  have hUle : Work.GW2.oddCoreIn H ≤ H := Subgroup.map_subtype_le (Work.GW2.oddCore ↥H)
  have hSle : S ≤ H := hUS ▸ le_sup_right
  -- Work inside `↥H`, where `U.subgroupOf H = O_{2'}(↥H)` is normal.
  have hU'eq : (Work.GW2.oddCoreIn H).subgroupOf H = Work.GW2.oddCore ↥H := by
    rw [Work.GW2.oddCoreIn, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hUnorm : ((Work.GW2.oddCoreIn H).subgroupOf H).Normal :=
    hU'eq ▸ Work.GW2.oddCore_normal ↥H
  have hUS' : (Work.GW2.oddCoreIn H).subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUle hSle, hUS, Subgroup.subgroupOf_self]
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.comap_subtype
  have hXcard : Nat.card (X.subgroupOf H) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  have hXodd' : Odd (Nat.card (X.subgroupOf H)) := hXcard.symm ▸ hXodd
  have hX' : X.subgroupOf H ≤ (Work.GW2.oddCoreIn H).subgroupOf H :=
    @le_of_sup_isPGroup ↥H _ _ ((Work.GW2.oddCoreIn H).subgroupOf H) (S.subgroupOf H)
      (X.subgroupOf H) hUnorm hUS' hS' hXodd'
  intro x hx
  have hmem : (⟨x, hXH hx⟩ : ↥H) ∈ X.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hX' hmem)

/-- **An odd-order element centralizing the Sylow `2`-subgroup `S` lies in `U = O(C_G(t))`.**

`c ∈ C_G(S)` has odd order, hence (as `S ≤ C_G(t)`) lies in `C_G(t) = O(C_G(t)) · S`; an
odd-order subgroup of such a product lies in the odd normal factor `O(C_G(t)) = D.U`. -/
theorem C_odd_mem_U {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2)
    {c : G} (hc : c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G))
    (hodd : Odd (orderOf c)) : c ∈ D.U := by
  -- `t ∈ S` and `t` is central in `S`, i.e. `S ≤ C_G(t) = D.H`
  have htS : D.t ∈ (D.S : Subgroup G) := D.S0_le D.t_mem
  have hSH : (D.S : Subgroup G) ≤ D.H := S_le_H D
  have hcomm : ∀ x ∈ (D.S : Subgroup G), x * D.t = D.t * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hSH hx) D.t (Set.mem_singleton D.t)).symm
  -- `C_G(t) = O(C_G(t)) · S` (Bender–Glauberman; here `D.U = O(C_G(t))`)
  have hsplit : Work.GW2.oddCoreIn D.H ⊔ (D.S : Subgroup G) = D.H :=
    Work.BG.SplitGlue.centralizerSplitProp G D.S D.n (by omega) D.dih D.t htS D.t_order hcomm
  -- `c` lies in `C_G(t) = D.H`
  have hct : D.t * c = c * D.t := Subgroup.mem_centralizer_iff.mp hc D.t htS
  have hcH : c ∈ D.H := by
    rw [show D.H = Subgroup.centralizer ({D.t} : Set G) from rfl]
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hct)
  -- the odd-order subgroup `⟨c⟩ ≤ D.H` therefore lies in `D.U`
  have hle : Subgroup.zpowers c ≤ Work.GW2.oddCoreIn D.H :=
    odd_subgroup_le_oddCoreIn D.H (D.S : Subgroup G) hsplit D.S.isPGroup'
      (Subgroup.zpowers c) (Subgroup.zpowers_le.mpr hcH) (by rw [Nat.card_zpowers]; exact hodd)
  exact hle (Subgroup.mem_zpowers c)

end Work.BG
