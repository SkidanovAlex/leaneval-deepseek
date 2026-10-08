import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

open Subgroup

set_option maxHeartbeats 1000000

/-- Every finite group of order `6` is solvable. -/
private theorem solvable_of_card_six {X : Type} [Group X] [Finite X] (h : Nat.card X = 6) :
    Group.IsSolvable X := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : 3 ∣ Nat.card X := by rw [h]; norm_num
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hPcard : Nat.card ↥(Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb]
  have hPindex : (Subgroup.zpowers b).index = 2 := by
    have hh := Subgroup.index_mul_card (Subgroup.zpowers b)
    rw [hPcard, h] at hh
    omega
  haveI : (Subgroup.zpowers b).Normal := Subgroup.normal_of_index_eq_two hPindex
  haveI hP3 : IsPGroup 3 ↥(Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  haveI : Group.IsNilpotent ↥(Subgroup.zpowers b) := hP3.isNilpotent
  haveI hQ2 : IsPGroup 2 (X ⧸ Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [← Subgroup.index_eq_card, hPindex]; norm_num)
  haveI : Group.IsNilpotent (X ⧸ Subgroup.zpowers b) := hQ2.isNilpotent
  exact Group.isSolvable_of_subgroup_quotient (Subgroup.zpowers b)

/-- **Bender 1981, Theorem 2.6, second alternative (p. 221), solvability form.**  If `O(M) = U`
for the Bender-setup subgroup `U = O(H)`, `O₂(M)` is a four-group and `|M : O₂(M)·O(M)| = 6`,
then `M` is solvable: it is an extension of the solvable group `O₂(M)·O(M)` (a four-group times an
odd-order group) by the group `M/O₂(M)O(M)` of order `6`.

An identical *private* lemma `solvable_of_case2` already exists in
`Submission/Work/CORE4/Case2NotHLeM.lean` (lines 182–268), proved with `I.toolkit.ft` in place of
`hFT`; this statement is its public, `FeitThompsonProp`-parameterised form and may be proved by
copying that argument, replacing the private helpers `odd_oddCore` / `oddCoreIn_odd'` of that file
by the public `Work.CORE4.oddCore_odd` / `Work.GW2.BenderSetup.U_odd` of the module
`Submission.Work.CORE4.Case2CountSetup` (and keeping the ~20-line `solvable_of_card_six` of that
file, which uses only Mathlib). -/
theorem solvable_of_fourGroup_oddCore_relIndex_six {G : Type} [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (B : Work.GW2.BenderSetup G) {M : Subgroup G}
    (hU : Work.GW2.oddCoreIn M = B.U)
    (hfour : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 M))
    (hrel : (Work.GW2.pCoreIn 2 M ⊔ B.U).relIndex M = 6) :
    Group.IsSolvable ↥M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the two pieces `P' = O₂(M)`, `Q' = O(M)` and their join, all inside `↥M`
  set P' : Subgroup ↥M := Work.GW2.pCore 2 ↥M with hP'def
  set Q' : Subgroup ↥M := Work.GW2.oddCore ↥M with hQ'def
  have hP'card : Nat.card ↥P' = 4 := by
    have h : Nat.card ↥(P'.map (Subgroup.subtype M)) = Nat.card ↥P' :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective M)
    rw [← h, hP'def]
    exact hfour.1
  have hQ'odd : Odd (Nat.card ↥Q') := by
    rw [hQ'def]
    exact Work.CORE4.oddCore_odd ↥M
  -- the index of `P' ⊔ Q'` in `↥M` is `6`
  have hPleM : Work.GW2.pCoreIn 2 M ≤ M := by
    rw [show Work.GW2.pCoreIn 2 M = P'.map (Subgroup.subtype M) from rfl]
    exact Subgroup.map_subtype_le _
  have hQleM : B.U ≤ M := by
    rw [← hU, Work.GW2.oddCoreIn]
    exact Subgroup.map_subtype_le _
  have hImg : (P' ⊔ Q').map (Subgroup.subtype M) = Work.GW2.pCoreIn 2 M ⊔ B.U := by
    have e1 : P'.map (Subgroup.subtype M) = Work.GW2.pCoreIn 2 M := rfl
    have e2 : Q'.map (Subgroup.subtype M) = B.U := by
      show (Work.GW2.oddCore ↥M).map (Subgroup.subtype M) = B.U
      exact hU
    rw [Subgroup.map_sup, e1, e2]
  have hKsub : (Work.GW2.pCoreIn 2 M ⊔ B.U).subgroupOf M = P' ⊔ Q' := by
    have h2 : ((Work.GW2.pCoreIn 2 M ⊔ B.U).subgroupOf M).map (Subgroup.subtype M)
        = Work.GW2.pCoreIn 2 M ⊔ B.U := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (sup_le hPleM hQleM)]
    have hcomap : Subgroup.comap (Subgroup.subtype M)
          (((Work.GW2.pCoreIn 2 M ⊔ B.U).subgroupOf M).map (Subgroup.subtype M))
        = Subgroup.comap (Subgroup.subtype M) ((P' ⊔ Q').map (Subgroup.subtype M)) := by
      rw [h2, hImg]
    rwa [Subgroup.comap_map_eq_self (by rw [Subgroup.ker_subtype]; exact bot_le),
      Subgroup.comap_map_eq_self (by rw [Subgroup.ker_subtype]; exact bot_le)] at hcomap
  have hK'index : (P' ⊔ Q').index = 6 := by
    rw [← hKsub]
    exact hrel
  have hK'card : Nat.card (↥M ⧸ (P' ⊔ Q')) = 6 := by
    rw [← Subgroup.index_eq_card]
    exact hK'index
  -- solvability of the three groups involved
  haveI : Group.IsSolvable ↥P' := by
    haveI h2 : IsPGroup 2 ↥P' := IsPGroup.of_card (n := 2) (by rw [hP'card]; norm_num)
    haveI h3 : Group.IsNilpotent ↥P' := h2.isNilpotent
    exact inferInstance
  haveI : Group.IsSolvable ↥Q' := hFT ↥Q' hQ'odd
  haveI : Group.IsSolvable (↥M ⧸ (P' ⊔ Q')) := solvable_of_card_six hK'card
  haveI : (P' : Subgroup ↥M).Normal := by rw [hP'def]; infer_instance
  haveI : (Q' : Subgroup ↥M).Normal := by rw [hQ'def]; infer_instance
  -- `(P' ⊔ Q')/P'` is a quotient of `Q'`
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (P'.subgroupOf (P' ⊔ Q'))).comp (Subgroup.inclusion le_sup_right)) := by
    intro y
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (P'.subgroupOf (P' ⊔ Q')) y
    obtain ⟨p, hp, q, hq, hpq⟩ := Subgroup.mem_sup_of_normal_left.mp z.2
    refine ⟨⟨q, hq⟩, ?_⟩
    rw [← hz]
    have hzprod : z = (⟨p, Subgroup.mem_sup_left hp⟩ : ↥(P' ⊔ Q')) *
        (⟨q, Subgroup.mem_sup_right hq⟩ : ↥(P' ⊔ Q')) := by
      apply Subtype.ext
      show (z : ↥M) = p * q
      rw [hpq]
    have hone : (QuotientGroup.mk' (P'.subgroupOf (P' ⊔ Q')))
        (⟨p, Subgroup.mem_sup_left hp⟩ : ↥(P' ⊔ Q')) = 1 :=
      (QuotientGroup.eq_one_iff (⟨p, Subgroup.mem_sup_left hp⟩ : ↥(P' ⊔ Q'))).mpr (by
        rw [Subgroup.mem_subgroupOf]
        exact hp)
    rw [hzprod, map_mul, hone, one_mul]
    refine congrArg (QuotientGroup.mk' (P'.subgroupOf (P' ⊔ Q'))) (Subtype.ext ?_)
    rfl
  have hK'solv : Group.IsSolvable ↥(P' ⊔ Q') := by
    haveI : Group.IsSolvable ((↥(P' ⊔ Q')) ⧸ (P'.subgroupOf (P' ⊔ Q'))) :=
      Group.isSolvable_of_surjective hsurj
    haveI : Group.IsSolvable ↥(P'.subgroupOf (P' ⊔ Q')) :=
      Group.isSolvable_of_surjective
        (f := ((Subgroup.subgroupOfEquivOfLe (le_sup_left : P' ≤ P' ⊔ Q')).symm).toMonoidHom)
        ((Subgroup.subgroupOfEquivOfLe (le_sup_left : P' ≤ P' ⊔ Q')).symm).surjective
    exact Group.isSolvable_of_subgroup_quotient (P'.subgroupOf (P' ⊔ Q'))
  exact Group.isSolvable_of_subgroup_quotient (P' ⊔ Q')

end Work.CORE4
