/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Extra

/-!
# CORE2A: the centralizer of a subgroup with a four-group is odd

`Work.CORE2A.odd_card_centralizer_of_four_subgroup`: if `E ≤ K` is a subgroup of a finite group
`K` whose Sylow 2-subgroups are cyclic or dihedral (`DihOrCycSylow K`), if `K` has 2-rank at
most two (`TwoRankProp`, i.e. every elementary abelian 2-subgroup of `K` has order at most `4`),
if `Z(E)` has odd order, and if `E` contains a Klein four-group `V`, then the centralizer
`C_K(E)` has odd order.

The argument is elementary.  If `C_K(E)` had even order, Cauchy's theorem would produce an
involution `x ∈ C_K(E)`.  Since `x` centralizes `E ⊇ V`, the subgroup `V ⊔ ⟨x⟩` is elementary
abelian; if `x ∉ V` it would have order `8`, contradicting the 2-rank bound.  Hence
`x ∈ V ≤ E`, so `x` is a *central* involution of `E`, and `2 ∣ |Z(E)|`, contradicting the
oddness of `Z(E)`.
-/

namespace Work.CORE2A

open Subgroup

/-- **Auxiliary.** If `V` is a Klein four-group and `x` is an involution commuting with every
element of `V`, then every element of the join `V ⊔ ⟨x⟩` squares to `1`; equivalently, `V ⊔ ⟨x⟩`
is elementary abelian (of exponent dividing `2`). -/
theorem sq_eq_one_of_mem_sup_zpowers_of_isFourGroup {K : Type} [Group K] {V : Subgroup K}
    (hV : Work.GW2.IsFourGroup V) {x : K} (hx2 : x ^ 2 = 1)
    (hxV : x ∈ Subgroup.centralizer (V : Set K)) :
    ∀ y ∈ (V ⊔ Subgroup.zpowers x : Subgroup K), y ^ 2 = 1 := by
  have hVcomm : IsMulCommutative V := IsFourGroup.isMulCommutative' hV
  have hzp : Subgroup.zpowers x ≤ Subgroup.centralizer (V : Set K) :=
    Subgroup.zpowers_le.mpr hxV
  have hDcomm : IsMulCommutative (V ⊔ Subgroup.zpowers x : Subgroup K) :=
    isMulCommutative_sup_of_le_centralizer hzp hVcomm
      (inferInstance : IsMulCommutative ↥(Subgroup.zpowers x))
  -- the subgroup of the join consisting of the elements that square to `1`
  let T : Subgroup K :=
    { carrier := {y : K | y ∈ (V ⊔ Subgroup.zpowers x : Subgroup K) ∧ y ^ 2 = 1}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haD, ha2⟩ := ha
        obtain ⟨hbD, hb2⟩ := hb
        have hcomm : Commute a b :=
          mul_comm_of_mem_of_isMulCommutative hDcomm haD hbD
        exact ⟨mul_mem haD hbD, by rw [hcomm.mul_pow 2, ha2, hb2, one_mul]⟩
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        intro a ha
        obtain ⟨haD, ha2⟩ := ha
        exact ⟨inv_mem haD, by rw [inv_pow, ha2, inv_one]⟩ }
  have hTmem : ∀ y : K, y ∈ T ↔ y ∈ (V ⊔ Subgroup.zpowers x : Subgroup K) ∧ y ^ 2 = 1 :=
    fun y => Iff.rfl
  have hVT : V ≤ T := by
    intro v hv
    exact ⟨Subgroup.mem_sup_left hv, hV.2 v hv⟩
  have hzpT : Subgroup.zpowers x ≤ T :=
    Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers x), hx2⟩
  have hDT : (V ⊔ Subgroup.zpowers x : Subgroup K) ≤ T := sup_le hVT hzpT
  intro y hy
  exact ((hTmem y).mp (hDT hy)).2

/-- **CORE2A.** Let `K` be a finite group with cyclic or dihedral Sylow 2-subgroups and 2-rank at
most two, and let `E ≤ K` be a subgroup with `Z(E)` of odd order containing a Klein four-group.
Then `C_K(E)` has odd order. -/
theorem odd_card_centralizer_of_four_subgroup {K : Type} [Group K] [Finite K] (E : Subgroup K)
    (hZodd : Odd (Nat.card (Subgroup.center ↥E)))
    (h2r : Work.GW2.TwoRankProp) (hsy : Work.GW2.DihOrCycSylow K)
    (hV : ∃ V : Subgroup K, V ≤ E ∧ Work.GW2.IsFourGroup V) :
    Odd (Nat.card (Subgroup.centralizer (E : Set K))) := by
  classical
  obtain ⟨V, hVE, hV4⟩ := hV
  by_contra hodd
  -- `C = C_K(E)`; assume it has even order, so it contains an involution `x`.
  let C : Subgroup K := Subgroup.centralizer (E : Set K)
  have hEven : Even (Nat.card ↥C) := by
    change Even (Nat.card (Subgroup.centralizer (E : Set K)))
    exact Nat.not_odd_iff_even.mp hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 (even_iff_two_dvd.mp hEven)
  have hxC : (x : K) ∈ Subgroup.centralizer (E : Set K) := x.2
  have hxK2 : (x : K) ^ 2 = 1 := by
    have h : (x : ↥C) ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val h
  -- `x` commutes with `V`, so `V ⊔ ⟨x⟩` is an elementary abelian `2`-subgroup of `K`.
  have hxV : (x : K) ∈ Subgroup.centralizer (V : Set K) :=
    Subgroup.centralizer_le hVE hxC
  have hD2 : ∀ y ∈ (V ⊔ Subgroup.zpowers (x : K) : Subgroup K), y ^ 2 = 1 :=
    sq_eq_one_of_mem_sup_zpowers_of_isFourGroup hV4 hxK2 hxV
  have hDcomm : IsMulCommutative (V ⊔ Subgroup.zpowers (x : K) : Subgroup K) :=
    isMulCommutative_sup_of_le_centralizer (Subgroup.zpowers_le.mpr hxV)
      (IsFourGroup.isMulCommutative' hV4)
      (inferInstance : IsMulCommutative ↥(Subgroup.zpowers (x : K)))
  -- the 2-rank bound (`TwoRankProp`) forces `V ⊔ ⟨x⟩ = V`.
  have hcardD : Nat.card ↥(V ⊔ Subgroup.zpowers (x : K) : Subgroup K) ≤ 4 :=
    h2r K hsy (V ⊔ Subgroup.zpowers (x : K)) hDcomm hD2
  have hVcard : Nat.card ↥V = 4 := IsFourGroup.card_eq hV4
  have h4le : 4 ≤ Nat.card ↥(V ⊔ Subgroup.zpowers (x : K) : Subgroup K) := by
    have hdvd : Nat.card ↥V ∣ Nat.card ↥(V ⊔ Subgroup.zpowers (x : K) : Subgroup K) :=
      Subgroup.card_dvd_of_le (le_sup_left : V ≤ (V ⊔ Subgroup.zpowers (x : K) : Subgroup K))
    rw [hVcard] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hVeq : V = (V ⊔ Subgroup.zpowers (x : K) : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge (le_sup_left : V ≤ (V ⊔ Subgroup.zpowers (x : K) : Subgroup K))
      (by rw [hVcard]; exact hcardD)
  have hxmemV : (x : K) ∈ V := by
    have hxD : (x : K) ∈ (V ⊔ Subgroup.zpowers (x : K) : Subgroup K) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : K))
    rwa [← hVeq] at hxD
  -- hence `x ∈ E` and is central in `E`, so `|Z(E)|` is even — contradiction.
  have hxE : (x : K) ∈ E := hVE hxmemV
  have hxcenter : (⟨(x : K), hxE⟩ : ↥E) ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa using (Subgroup.mem_centralizer_iff.mp hxC) (g : K) g.2
  have hxKord : orderOf (x : K) = 2 := by
    rw [← Subgroup.orderOf_mk (x : K) x.2]
    exact hx2
  have hordE : orderOf (⟨(x : K), hxE⟩ : ↥E) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hxKord
  have h2dvdZ : 2 ∣ Nat.card (Subgroup.center ↥E) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥E) hxcenter
    rwa [hordE] at this
  exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h2dvdZ)

end Work.CORE2A
