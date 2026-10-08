import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.PSU3.StageB.fixedPts_card_and_centralizer_index
import Submission.Work.GroupTheory.exists_pair_mem_of_odd_index
import Submission.Work.GroupTheory.index_inf_subgroupOf_dvd_index_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.nprime_ge_two`

For `P ≤ V = C_D(t)` of prime order (`P ≠ ⊥`) and `y ∈ Q ∖ Q₀` centralising `P`, the cardinality
`|C_{Q₀}(P)| = |Q₀sub H ⊓ C_G(P)|` is `2^{n'}` with `n' ≥ 2`.

The argument never uses the classification: `Q ⊓ C_G(P)` is a Sylow `2`-subgroup of `C_G(P)`
(it is a `2`-group, and its index there is `|Ω^P| · [C_H(P) : C_Q(P)]`, a product of two odd
numbers: oddness of `|Ω^P| = |C_Q(P)| + 1` is `fixedPts_card_and_centralizer_index`, and
`[C_H(P) : C_Q(P)] ∣ [H : Q] = |D|` is the second isomorphism theorem,
`index_inf_subgroupOf_dvd_index_subgroupOf`).  Hypothesis (B3) supplies a four-group in `C_G(P)`,
which `exists_pair_mem_of_odd_index` conjugates into that Sylow subgroup `C_Q(P) ≤ Q`; the two
commuting involutions obtained lie in `Q₀sub H = Ω₁(Q)` and centralise `P`, so they give four
distinct elements of `C_{Q₀}(P)`: `|C_{Q₀}(P)| ≥ 4`.  Finally `Q₀sub H` has exponent `2`
(elementary abelian, `Work.ThmF.L5.Q0sub_elementary`), so `C_{Q₀}(P)` is a `2`-group, its order
is `2^{n'}`, and `4 ≤ 2^{n'}` gives `n' ≥ 2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem nprime_ge_two {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {P : Subgroup G}
    (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime) (hPne : P ≠ ⊥)
    {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y) :
    ∃ n' : ℕ, 2 ≤ n' ∧
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) = 2 ^ n' := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup G := Subgroup.centralizer (P : Set G)
  let QL : Subgroup G := Q ⊓ L
  -- ## `y` witnesses `y ∈ QL ∖ {1}`
  have hyL : y ∈ L := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h := hyc p hp
    calc p * y = p * (p⁻¹ * y * p) := by rw [h]
      _ = y * p := by group
  have hyQL : y ∈ QL := Subgroup.mem_inf.mpr ⟨hyQ, hyL⟩
  have hy_ne_one : y ≠ 1 := by
    intro h
    exact hy0 (by rw [h]; exact (Work.ThmF.Q0sub H).one_mem)
  -- ## the fixed-point count and the orbit–stabiliser identity
  have hfixed : (fixedPts H P).ncard = Nat.card ↥QL + 1 ∧
      Nat.card ↥L = Nat.card ↥(H ⊓ L) * (fixedPts H P).ncard ∧
      Odd ((fixedPts H P).ncard) :=
    fixedPts_card_and_centralizer_index hS hC4 hPV hPne
  -- ## `Q ⊓ C_G(P)` is a `2`-group
  have hQL_pgroup : IsPGroup 2 ↥QL := by
    intro x
    obtain ⟨n, hn⟩ := hS.two (⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩ : ↥Q)
    refine ⟨n, ?_⟩
    apply Subtype.ext
    have h2 := congrArg (fun g : ↥Q => (g : G)) hn
    simpa using h2
  -- ## `|C_H(P) : C_Q(P)|` is odd, being a divisor of `|H : Q| = |D|`
  have hinf_eq : (H ⊓ L) ⊓ Q = QL := by
    show (H ⊓ L) ⊓ Q = Q ⊓ L
    ext x
    constructor
    · intro hx
      exact ⟨(Subgroup.mem_inf.mp hx).2, (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2⟩
    · intro hx
      obtain ⟨hxQ, hxL⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_inf.mpr ⟨hS.split.le hxQ, hxL⟩, hxQ⟩
  have hdvd : (QL.subgroupOf (H ⊓ L)).index ∣ (Q.subgroupOf H).index := by
    rw [← hinf_eq]
    exact Work.GroupTheory.index_inf_subgroupOf_dvd_index_subgroupOf (Q := Q) (H := H)
      (M := H ⊓ L) hS.split.le inf_le_left hS.split.normal
  have hQHidx : (Q.subgroupOf H).index = Nat.card ↥(twoPoint H t) := by
    have hcard := Subgroup.card_mul_index (Q.subgroupOf H)
    have h1 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.split.le).toEquiv
    rw [h1, Work.ThmF.card_H_eq_mul_of_data (Work.ThmF.IsSplitRankOne.toData hS.split)]
      at hcard
    exact Nat.mul_left_cancel Nat.card_pos hcard
  have hQHidx_odd : Odd ((Q.subgroupOf H).index) := by
    rw [hQHidx]; exact Work.ThmF.split_odd_card_twoPoint hS.split
  have hd_odd : Odd (QL.subgroupOf (H ⊓ L)).index := by
    have h2 : (2 : ℕ) ∣ (QL.subgroupOf (H ⊓ L)).index → Even ((Q.subgroupOf H).index) :=
      fun h => even_iff_two_dvd.mpr (dvd_trans h hdvd)
    exact Nat.not_even_iff_odd.mp
      (fun he => (Nat.not_even_iff_odd.mpr hQHidx_odd) (h2 (even_iff_two_dvd.mp he)))
  -- ## therefore `Q ⊓ C_G(P)` has odd index in `L = C_G(P)`
  have hL_le : QL ≤ H ⊓ L := le_inf (inf_le_left.trans hS.split.le) inf_le_right
  have hidx_odd : Odd ((QL.subgroupOf L).index) := by
    have hc1 : Nat.card ↥(QL.subgroupOf L) = Nat.card ↥QL :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : QL ≤ L)).toEquiv
    have hc2 : Nat.card ↥(QL.subgroupOf (H ⊓ L)) = Nat.card ↥QL :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL_le).toEquiv
    have hcardL := Subgroup.card_mul_index (QL.subgroupOf L)
    rw [hc1] at hcardL
    have hcardM := Subgroup.card_mul_index (QL.subgroupOf (H ⊓ L))
    rw [hc2] at hcardM
    have hmain : Nat.card ↥QL * (QL.subgroupOf L).index
        = Nat.card ↥QL * ((QL.subgroupOf (H ⊓ L)).index * (fixedPts H P).ncard) := by
      calc Nat.card ↥QL * (QL.subgroupOf L).index = Nat.card ↥L := hcardL
        _ = Nat.card ↥(H ⊓ L) * (fixedPts H P).ncard := hfixed.2.1
        _ = (Nat.card ↥QL * (QL.subgroupOf (H ⊓ L)).index) * (fixedPts H P).ncard := by
              rw [hcardM]
        _ = Nat.card ↥QL * ((QL.subgroupOf (H ⊓ L)).index * (fixedPts H P).ncard) := by ring
    have := Nat.mul_left_cancel Nat.card_pos hmain
    rw [this]
    exact hd_odd.mul hfixed.2.2
  have hQL2 : IsPGroup 2 ↥(QL.subgroupOf L) := by
    obtain ⟨k, hk⟩ := hQL_pgroup.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : QL ≤ L)).toEquiv, hk]
  -- ## (B3) gives a four-group in `C_G(P)`, which conjugates into `Q ⊓ C_G(P)`
  obtain ⟨a, b, ha2, hb2, hab_ne, hab_comm⟩ := hS.B3 P hPV hPp
  have hpair : ∃ a' ∈ QL.subgroupOf L, ∃ b' ∈ QL.subgroupOf L,
      orderOf a' = 2 ∧ orderOf b' = 2 ∧ a' ≠ b' ∧ a' * b' = b' * a' :=
    Work.GroupTheory.exists_pair_mem_of_odd_index hQL2 hidx_odd ha2 hb2 hab_ne hab_comm
  obtain ⟨a', ha'T, b', hb'T, ha'2, hb'2, ha'b', ha'comm⟩ := hpair
  have ha'QL : (a' : G) ∈ QL := Subgroup.mem_subgroupOf.mp ha'T
  have hb'QL : (b' : G) ∈ QL := Subgroup.mem_subgroupOf.mp hb'T
  have ha'Q : (a' : G) ∈ Q := (Subgroup.mem_inf.mp ha'QL).1
  have hb'Q : (b' : G) ∈ Q := (Subgroup.mem_inf.mp hb'QL).1
  have ha'L : (a' : G) ∈ L := (Subgroup.mem_inf.mp ha'QL).2
  have hb'L : (b' : G) ∈ L := (Subgroup.mem_inf.mp hb'QL).2
  have haG2 : orderOf (a' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ha'2
  have hbG2 : orderOf (b' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hb'2
  have haQ0 : (a' : G) ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H ⟨hS.split.le ha'Q, haG2⟩)
  have hbQ0 : (b' : G) ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H ⟨hS.split.le hb'Q, hbG2⟩)
  -- ## four distinct elements of `Q₀sub H ⊓ C_G(P)`
  have haI : (a' : G) ∈ Work.ThmF.Q0sub H ⊓ L := Subgroup.mem_inf.mpr ⟨haQ0, ha'L⟩
  have hbI : (b' : G) ∈ Work.ThmF.Q0sub H ⊓ L := Subgroup.mem_inf.mpr ⟨hbQ0, hb'L⟩
  have habI : (a' : G) * (b' : G) ∈ Work.ThmF.Q0sub H ⊓ L := mul_mem haI hbI
  have h1I : (1 : G) ∈ Work.ThmF.Q0sub H ⊓ L := (Work.ThmF.Q0sub H ⊓ L).one_mem
  have ha_sq : (a' : G) * (a' : G) = 1 := by
    have h := pow_orderOf_eq_one (a' : G); rw [haG2] at h; simpa [pow_two] using h
  have hb_sq : (b' : G) * (b' : G) = 1 := by
    have h := pow_orderOf_eq_one (b' : G); rw [hbG2] at h; simpa [pow_two] using h
  have ha_ne_one : (a' : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at haG2; exact absurd haG2 (by norm_num)
  have hb_ne_one : (b' : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hbG2; exact absurd hbG2 (by norm_num)
  have ha_ne_b : (a' : G) ≠ (b' : G) := fun h => ha'b' (Subtype.ext h)
  have hab_ne_one : (a' : G) * (b' : G) ≠ 1 := by
    intro h
    have hb_eq : (b' : G) = (a' : G) := by
      have h1 : (b' : G) = (a' : G)⁻¹ := eq_inv_of_mul_eq_one_right h
      rwa [inv_eq_of_mul_eq_one_right ha_sq] at h1
    exact ha_ne_b hb_eq.symm
  have ha_ne_ab : (a' : G) ≠ (a' : G) * (b' : G) := by
    intro h
    have h2 : (b' : G) = 1 := by
      calc (b' : G) = (a' : G)⁻¹ * ((a' : G) * (b' : G)) := by group
        _ = (a' : G)⁻¹ * (a' : G) := by rw [← h]
        _ = 1 := inv_mul_cancel _
    exact hb_ne_one h2
  have hb_ne_ab : (b' : G) ≠ (a' : G) * (b' : G) := by
    intro h
    have h2 : (a' : G) = 1 := by
      calc (a' : G) = ((a' : G) * (b' : G)) * (b' : G)⁻¹ := by group
        _ = (b' : G) * (b' : G)⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel _
    exact ha_ne_one h2
  have hcard4 : ({(1 : G), (a' : G), (b' : G), (a' : G) * (b' : G)} : Set G).ncard = 4 := by
    have h1 : (1 : G) ∉ ({(a' : G), (b' : G), (a' : G) * (b' : G)} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => ha_ne_one h.symm, fun h => hb_ne_one h.symm, fun h => hab_ne_one h.symm⟩
    have h2 : (a' : G) ∉ ({(b' : G), (a' : G) * (b' : G)} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha_ne_b, ha_ne_ab⟩
    have h3 : (b' : G) ∉ ({(a' : G) * (b' : G)} : Set G) := by
      simp only [Set.mem_singleton_iff]
      exact hb_ne_ab
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
        Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  have hsub : ({(1 : G), (a' : G), (b' : G), (a' : G) * (b' : G)} : Set G) ⊆
      ((Work.ThmF.Q0sub H ⊓ L : Subgroup G) : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [h1I, haI, hbI, habI]
  have hI_card : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H ⊓ L) := by
    have h2 : Nat.card ↥(Work.ThmF.Q0sub H ⊓ L)
        = ((Work.ThmF.Q0sub H ⊓ L : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
    rw [h2]
    calc 4 = ({(1 : G), (a' : G), (b' : G), (a' : G) * (b' : G)} : Set G).ncard := hcard4.symm
      _ ≤ ((Work.ThmF.Q0sub H ⊓ L : Subgroup G) : Set G).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
  -- ## `Q₀sub H` has exponent `2`, so `C_{Q₀}(P)` is a `2`-group of order `4 ≤ 2^{n'}`
  have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hS.split
  have hQ0el := Work.ThmF.L5.Q0sub_elementary hcomm
  have hI2 : IsPGroup 2 ↥(Work.ThmF.Q0sub H ⊓ L) := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have hxQ0 : (x : G) ∈ Work.ThmF.Q0sub H := (Subgroup.mem_inf.mp x.2).1
    have hxx : (x : G) * (x : G) = 1 := hQ0el.1 (x : G) hxQ0
    show ((x : G)) ^ 2 ^ 1 = (1 : G)
    rw [pow_one, pow_two]
    exact hxx
  obtain ⟨n', hn'⟩ := hI2.exists_card_eq
  refine ⟨n', ?_, hn'⟩
  have hge : 2 ^ 2 ≤ 2 ^ n' := by
    rw [← hn']
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4]
    exact hI_card
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hge

end Work.PSU3.StageB
