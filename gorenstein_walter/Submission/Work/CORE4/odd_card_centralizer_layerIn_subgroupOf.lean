import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.RED.DihedralFacts
import Submission.Work.RED.odd_card_centralizer_of_four_subgroup

namespace Work.CORE4

open scoped MatrixGroups

open Subgroup

set_option linter.style.haveILetI false

/-- A finite cyclic group all of whose elements are involutions has order at most `2`: if `g`
generates it, then `g ^ 2 = 1`, so `orderOf g ∣ 2`, while `orderOf g = |H|`. -/
theorem card_le_two_of_isCyclic_sq_eq_one {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (h : ∀ x : H, x ^ 2 = 1) : Nat.card H ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have htop : Subgroup.zpowers g = ⊤ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => hg x⟩
  have hord : orderOf g = Nat.card H := by
    rw [← Nat.card_zpowers (a := g), htop, Subgroup.card_top]
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h g)
  calc Nat.card H = orderOf g := hord.symm
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd

/-- The centralizer (inside `M = C.D.M`) of the layer `E(M) = layerIn C.D.M` has odd order.

`Z(E(M)) = 1` and `E(M)` contains a Klein four-group `V`; `Syl₂(M)` is cyclic or dihedral because
`M ≤ G` and `Syl₂(G)` is (`DihOrCycSub`).  If `|C_M(E(M))|` were even, an involution `z` of it
(together with a Sylow 2-subgroup containing the elementary abelian subgroup `W = V · ⟨z⟩` of order
`8`) would force `Syl₂(M)` to be non-cyclic, hence dihedral, contradicting the 2-rank bound in
dihedral groups. -/
theorem odd_card_centralizer_layerIn_subgroupOf {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (C : Work.GW2.Case2Ctx6 B) (hbc : Work.GW2.BenderCtx G)
    (hZ : Subgroup.center ↥((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) = ⊥)
    (hV : ∃ V : Subgroup ↥C.D.M,
      V ≤ (Work.GW2.layerIn C.D.M).subgroupOf C.D.M ∧ Work.GW2.IsFourGroup V) :
    Odd (Nat.card (Subgroup.centralizer
      (((Work.GW2.layerIn C.D.M).subgroupOf C.D.M : Subgroup ↥C.D.M) : Set ↥C.D.M))) := by
  obtain ⟨V, hVle, hV4⟩ := hV
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  -- an involution `z` of `C_M(E(M))`
  obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' 2 hodd
  have hz2' : orderOf (z : ↥C.D.M) = 2 := by rw [orderOf_coe, hz2]
  -- `V · ⟨z⟩` is elementary abelian of order `8`
  obtain ⟨W, hWcard, hWsq⟩ :=
    Work.RED.exists_elementary_abelian_eight_of_involution
      ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) hZ hVle hV4 z.2 hz2'
  -- it lies in a Sylow `2`-subgroup `P` of `↥M`
  have hWpg : IsPGroup 2 ↥W := IsPGroup.of_card (n := 3) (by rw [hWcard]; norm_num)
  obtain ⟨P, hWP⟩ := hWpg.exists_le_sylow
  rcases Work.CORE4.DihOrCycSub hbc.sylow C.D.M P with hcyc | ⟨n, ⟨e⟩⟩
  · -- `P` cyclic is impossible: then `W` would be cyclic of order `8` with all squares `1`
    haveI : IsCyclic ↥(P : Subgroup ↥C.D.M) := hcyc
    haveI : IsCyclic ↥(W.subgroupOf P) := inferInstance
    haveI : IsCyclic ↥W :=
      (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hWP)).mp inferInstance
    have h2 : Nat.card ↥W ≤ 2 :=
      card_le_two_of_isCyclic_sq_eq_one (H := ↥W) (fun w => by
        apply Subtype.ext
        simpa [Subgroup.coe_pow] using hWsq w w.2)
    omega
  · -- `P` dihedral: its 2-rank is at most `2`, contradicting `W`
    haveI : NeZero n := Work.RED.GW2.neZero_of_mulEquiv_dihedral e
    exact Work.RED.no_elementary_abelian_eight Work.RED.DihedralFacts e ⟨W, hWcard, hWsq⟩

end Work.CORE4
