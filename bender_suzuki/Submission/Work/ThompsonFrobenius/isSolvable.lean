import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.npc_quotient
import Submission.Work.ThompsonFrobenius.pCore_lt
import Submission.Work.ThompsonFrobenius.commutator_le
import Submission.Work.HallHigman.ModRep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-7a: the minimal counterexample is solvable (area `ThompsonFrobenius`)

Step GT-7a of `NOTES_LEAD_bs_thompson.md`.  With `H = O_p(G)` and `K` the preimage of the normal
`p`-complement of `G/H` (GT-3), the normal series `1 ≤ H ≤ K ≤ G` has factors

* `H`, a `p`-group (hence nilpotent, hence solvable);
* `K/H`, abelian: `commutator ↥K ≤ H.subgroupOf K` since `⁅K,K⁆ ≤ O_p(G)` (GT-6);
* `G/K`, a `p`-group (GT-3 again: `G/K ≅ (G/H)/(K/H)`).

So `K` is solvable and then `G` is solvable.
-/

set_option autoImplicit false

open scoped Pointwise commutatorElement

namespace Work.ThompsonFrobenius

theorem isSolvable {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) : Group.IsSolvable G := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let H : Subgroup G := Work.HallHigman.pCore p G
  haveI hHnormal : H.Normal := inferInstance
  have hHpg : IsPGroup p H := Work.HallHigman.isPGroup_pCore
  obtain ⟨Mbar, hMbar⟩ := npc_quotient h
  haveI hMbarnormal : Mbar.Normal := hMbar.normal
  let K : Subgroup G := Mbar.comap (QuotientGroup.mk' H)
  haveI hKnormal : K.Normal := Subgroup.normal_comap _
  have hHK : H ≤ K := by
    intro x hx
    show (QuotientGroup.mk' H) x ∈ Mbar
    have h1 : (QuotientGroup.mk' H) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    simpa [h1] using Mbar.one_mem
  have hKmap : Subgroup.map (QuotientGroup.mk' H) K = Mbar := by
    show Subgroup.map (QuotientGroup.mk' H) (Mbar.comap (QuotientGroup.mk' H)) = Mbar
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective H),
      top_inf_eq]
  -- GT-6
  have hcomm : ⁅K, K⁆ ≤ H := commutator_le h (show Work.NPC.IsNormalPComplement p
    (K.map (QuotientGroup.mk' H)) from hKmap.symm ▸ hMbar) hHK
  -- `K/H` is abelian
  have hcomm' : _root_.commutator ↥K ≤ H.subgroupOf K := by
    show _root_.commutator ↥K ≤ H.comap K.subtype
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_subtype_commutator]
    exact hcomm
  haveI : IsMulCommutative (↥K ⧸ H.subgroupOf K) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm'
  -- `K` is solvable
  have hHsubpg : IsPGroup p (H.subgroupOf K) := hHpg.comap_subtype
  haveI : Group.IsSolvable ↥(H.subgroupOf K) := by
    haveI : Group.IsNilpotent ↥(H.subgroupOf K) := hHsubpg.isNilpotent
    infer_instance
  have hKsolv : Group.IsSolvable ↥K := Group.isSolvable_of_subgroup_quotient (H.subgroupOf K)
  -- `G/K` is a `p`-group, hence solvable
  have hGKpg : IsPGroup p (G ⧸ K) := by
    have hiso : (G ⧸ H) ⧸ Mbar ≃* G ⧸ K :=
      (QuotientGroup.quotientMulEquivOfEq hKmap).symm.trans
        (QuotientGroup.quotientQuotientEquivQuotient H K hHK)
    exact IsPGroup.of_equiv hMbar.isPGroup_quotient hiso
  haveI : Group.IsSolvable (G ⧸ K) := by
    haveI : Group.IsNilpotent (G ⧸ K) := hGKpg.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient K

end Work.ThompsonFrobenius
