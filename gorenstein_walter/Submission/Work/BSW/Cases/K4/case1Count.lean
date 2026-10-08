/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein-Walter formalisation team (area BSW, the `|K| = 4` case)

# Bender's Case 1: the two counting lemmas

* `case1H_coset_involutions_aux`: for an involution `u` outside `H = C_G(X)⟨t⟩` that inverts no
  nontrivial element of `A = C_G(X)`, the coset `H u` contains exactly `|C_H(u)|` involutions.
* `case1_bCount_two_aux`: Bender's double count `bCount H 2 = 2 |A|`: the pairs `(z, u)` with `z`
  an involution of `H`, `u` an involution outside `H`, commuting, are counted in two ways.
-/
import Mathlib
import Submission.Work.BSW.Cases.K4.case1Aux
import Submission.Work.BSW.Cases.K4.ncard_involutions_coset_eq
import Submission.Work.BSW.Cases.K4.case1H_U2_card
import Submission.Work.BSW.Cases.K4.case1H_centralizer_le_two
import Submission.Work.COPR.card_mul_of_fibers

namespace Work.BSW.Cases.K4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- The pairs `(z, u)` with `z` an involution of `H` and `u` an involution outside `H`, that
commute. -/
def case1PairSet (X : Subgroup G) (t : G) : Set (G × G) :=
  {p | p.1 ∈ case1H X t ∧ orderOf p.1 = 2 ∧ p.2 ∉ case1H X t ∧ orderOf p.2 = 2 ∧
    p.1 * p.2 = p.2 * p.1}

/-- A subgroup of order `2` has a nonidentity element. -/
theorem exists_ne_one_of_card_eq_two {C : Subgroup G} (hC : Nat.card ↥C = 2) :
    ∃ z ∈ C, z ≠ 1 := by
  haveI : Fintype ↥C := Fintype.ofFinite _
  have h : 1 < Fintype.card ↥C := by rw [← Nat.card_eq_fintype_card, hC]; norm_num
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h
  by_cases ha : (a : G) = 1
  · exact ⟨(b : G), b.2, fun hb => hab (Subtype.ext (by rw [ha, hb]))⟩
  · exact ⟨(a : G), a.2, ha⟩

/-- In a subgroup of order `2` there is at most one nonidentity element. -/
theorem eq_of_ne_one_of_card_eq_two {C : Subgroup G} (hC : Nat.card ↥C = 2) {a b : G}
    (ha : a ∈ C) (ha1 : a ≠ 1) (hb : b ∈ C) (hb1 : b ≠ 1) : a = b := by
  have hsub : ({1, a} : Set G) ⊆ (C : Set G) := by
    rintro x (rfl | rfl)
    · exact C.one_mem
    · exact ha
  have hcard1 : ({1, a} : Set G).ncard = 2 := Set.ncard_pair (fun h => ha1 h.symm)
  have hcardC : (C : Set G).ncard = 2 := by
    rw [← Nat.card_coe_set_eq (C : Set G)]
    exact hC
  have heq : ({1, a} : Set G) = (C : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [hcard1, hcardC]
  have hb' : b ∈ ({1, a} : Set G) := heq ▸ hb
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
  rcases hb' with h | h
  · exact absurd h hb1
  · exact h.symm

/-- The coset `H u` of an involution `u` outside `H` that inverts no nontrivial element of `A`
contains exactly `|C_H(u)|` involutions. -/
theorem case1H_coset_involutions_aux (h : K4Hyp G) (X : Subgroup G) (t : G)
    (hX3 : Nat.card ↥X = 3) (ht2 : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (X : Set G)) {u : G} (hu2 : orderOf u = 2)
    (huH : u ∉ case1H X t)
    (hinv : ∀ a ∈ case1A X, a ≠ 1 → u * a * u⁻¹ ≠ a⁻¹) :
    ({y : G | orderOf y = 2 ∧ ∃ k ∈ case1H X t, y = k * u} : Set G).ncard =
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) := by
  have htinv := (case1A_comm_and_inv h hX3 ht2 htN).2
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have htinv' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have huu : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have huu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hle2 := case1H_centralizer_le_two h X t hX3 ht2 htN hu2 huH
  -- `{y ∈ H : u y u = y⁻¹}` is exactly `C_H(u)`
  have hset : ({y : G | y ∈ case1H X t ∧ u * y * u = y⁻¹} : Set G) =
      ((Subgroup.centralizer ({u} : Set G) ⊓ case1H X t : Subgroup G) : Set G) := by
    ext y
    constructor
    · rintro ⟨hyH, hyinv⟩
      have hy' : y ∈ (Subgroup.centralizer ({u} : Set G) ⊓ case1H X t : Subgroup G) := by
        rw [Subgroup.mem_inf]
        refine ⟨?_, hyH⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        rcases (mem_case1H_iff ht2 htN).mp hyH with hyA | ⟨a, ha, rfl⟩
        · have hy1 : y = 1 := by
            by_contra hy1
            refine hinv y hyA hy1 ?_
            rw [huu']
            exact hyinv
          rw [hy1, one_mul, mul_one]
        · have htat : t * a * t = a⁻¹ := by
            calc t * a * t = t * a * t⁻¹ := by rw [htinv']
              _ = a⁻¹ := htinv a ha
          have hsq : (a * t) * (a * t) = 1 := by
            calc (a * t) * (a * t) = a * (t * a * t) := by group
              _ = a * a⁻¹ := by rw [htat]
              _ = 1 := mul_inv_cancel a
          have hinv2 : ((a * t) : G)⁻¹ = a * t := inv_eq_of_mul_eq_one_right hsq
          have h1 : u * (a * t) * u = a * t := by rw [hyinv, hinv2]
          show (a * t) * u = u * (a * t)
          calc (a * t) * u = ((u * (a * t) * u) * u) := by rw [h1]
            _ = u * (a * t) * (u * u) := by group
            _ = u * (a * t) := by rw [huu, mul_one]
      exact hy'
    · intro hy
      have hy' : y ∈ (Subgroup.centralizer ({u} : Set G) ⊓ case1H X t : Subgroup G) := hy
      obtain ⟨hyC, hyH⟩ := Subgroup.mem_inf.mp hy'
      have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      refine ⟨hyH, ?_⟩
      have hy2 : y * y = 1 := by
        have hdvd : orderOf y ∣
            Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) :=
          orderOf_dvd_natCard_of_mem hy'
        have hle : orderOf y ≤ 2 := le_trans (Nat.le_of_dvd Nat.card_pos hdvd) hle2
        have hpos : 0 < orderOf y := orderOf_pos_iff.mpr (isOfFinOrder_of_finite y)
        rcases (by omega : orderOf y = 1 ∨ orderOf y = 2) with h1 | h1
        · rw [orderOf_eq_one_iff.mp h1, one_mul]
        · have hd : orderOf y ∣ 2 := h1 ▸ dvd_rfl
          have hpow := orderOf_dvd_iff_pow_eq_one.mp hd
          rwa [pow_two] at hpow
      calc u * y * u = y * u * u := by rw [← hyu]
        _ = y := by rw [mul_assoc, huu, mul_one]
        _ = y⁻¹ := (inv_eq_of_mul_eq_one_right hy2).symm
  rw [ncard_involutions_coset_eq (case1H X t) u hu2 huH, hset]
  exact (Nat.card_coe_set_eq
    ((Subgroup.centralizer ({u} : Set G) ⊓ case1H X t : Subgroup G) : Set G)).symm

/-- Bender's double count: `bCount H 2 = 2 |A|`. -/
theorem case1_bCount_two_aux (h : K4Hyp G) (X : Subgroup G) (t : G) (hX3 : Nat.card ↥X = 3)
    (ht2 : orderOf t = 2) (htN : t ∈ Subgroup.normalizer (X : Set G))
    (hpartners : ∀ z ∈ case1H X t, orderOf z = 2 →
      ({u : G | u ∉ case1H X t ∧ orderOf u = 2 ∧ z * u = u * z} : Set G).ncard = 4)
    (hle2 : ∀ u : G, u ∉ case1H X t → orderOf u = 2 →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) ≤ 2)
    (hcoset : ∀ u : G, orderOf u = 2 → u ∉ case1H X t →
      ({y : G | orderOf y = 2 ∧ ∃ k ∈ case1H X t, y = k * u} : Set G).ncard =
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t)) :
    Work.GW2.bCount (case1H X t) 2 = 2 * Nat.card ↥(case1A X) := by
  classical
  have hJH : ({x : G | orderOf x = 2 ∧ x ∈ case1H X t} : Set G).ncard =
      Nat.card ↥(case1A X) := case1H_involutions h hX3 ht2 htN
  have hmem : ∀ p : ↥(case1PairSet X t),
      (p : G × G).1 ∈ case1H X t ∧ orderOf (p : G × G).1 = 2 ∧
        (p : G × G).2 ∉ case1H X t ∧ orderOf (p : G × G).2 = 2 ∧
        (p : G × G).1 * (p : G × G).2 = (p : G × G).2 * (p : G × G).1 := fun p => p.2
  have hβ : Nat.card {z : G // z ∈ case1H X t ∧ orderOf z = 2} = Nat.card ↥(case1A X) := by
    have h1 : Nat.card {z : G // z ∈ case1H X t ∧ orderOf z = 2} =
        ({z : G | z ∈ case1H X t ∧ orderOf z = 2} : Set G).ncard := Nat.card_coe_set_eq _
    have h2 : ({z : G | z ∈ case1H X t ∧ orderOf z = 2} : Set G) =
        {z : G | orderOf z = 2 ∧ z ∈ case1H X t} := by
      ext x
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [h1, h2, hJH]
  -- the `|C_H(u)| = 2` condition characterises the pairs
  have hcard2 : ∀ p : ↥(case1PairSet X t),
      Nat.card ↥(Subgroup.centralizer ({(p : G × G).2} : Set G) ⊓ case1H X t) = 2 := by
    intro p
    have hle := hle2 (p : G × G).2 (hmem p).2.2.1 (hmem p).2.2.2.1
    have hp : (p : G × G).1 ∈
        Subgroup.centralizer ({(p : G × G).2} : Set G) ⊓ case1H X t := by
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hmem p).2.2.2.2, (hmem p).1⟩
    have hp1 : (p : G × G).1 ≠ 1 := by
      intro h1
      have h2 := (hmem p).2.1
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have hne1 : Nat.card ↥(Subgroup.centralizer ({(p : G × G).2} : Set G) ⊓ case1H X t) ≠ 1 := by
      intro h1
      have hbot : (Subgroup.centralizer ({(p : G × G).2} : Set G) ⊓ case1H X t) = ⊥ :=
        Subgroup.eq_bot_of_card_eq _ h1
      have hmem_bot : (p : G × G).1 ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hp
      exact hp1 (Subgroup.mem_bot.mp hmem_bot)
    have hne0 : Nat.card ↥(Subgroup.centralizer ({(p : G × G).2} : Set G) ⊓ case1H X t) ≠ 0 :=
      Nat.card_pos.ne'
    omega
  -- the `z`-fibres have four elements each
  have hfib : ∀ z : {z : G // z ∈ case1H X t ∧ orderOf z = 2},
      Nat.card {p : ↥(case1PairSet X t) //
        (⟨(p : G × G).1, (hmem p).1, (hmem p).2.1⟩ :
          {z : G // z ∈ case1H X t ∧ orderOf z = 2}) = z} = 4 := by
    intro z
    rw [← hpartners z.1 z.2.1 z.2.2]
    apply Nat.card_congr
    refine
      { toFun := fun p => ⟨(p.1 : G × G).2, (hmem p.1).2.2.1, (hmem p.1).2.2.2.1, ?_⟩
        invFun := fun u => ⟨⟨((z : G), (u : G)),
          ⟨z.2.1, z.2.2, u.2.1, u.2.2.1, u.2.2.2⟩⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hv : (p.1 : G × G).1 = (z : G) := congrArg Subtype.val p.2
      have hc := (hmem p.1).2.2.2.2
      rw [hv] at hc
      exact hc
    · apply Subtype.ext
      rfl
    · intro p
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (congrArg Subtype.val p.2).symm rfl
    · intro u
      apply Subtype.ext
      rfl
  have hPcard : Nat.card ↥(case1PairSet X t) = 4 * Nat.card ↥(case1A X) := by
    have hcard := Work.COPR.card_mul_of_fibers
      (fun q : ↥(case1PairSet X t) =>
        (⟨(q : G × G).1, (hmem q).1, (hmem q).2.1⟩ :
          {z : G // z ∈ case1H X t ∧ orderOf z = 2}))
      4 hfib
    rw [hcard, hβ, Nat.mul_comm]
  -- the `u`-fibres are singletons, giving a bijection with the set counted by `case1H_U2_card`
  have hbij : Nat.card ↥(case1PairSet X t) = Nat.card
      {u : G // u ∉ case1H X t ∧ orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) = 2} := by
    apply Nat.card_congr
    refine Equiv.ofBijective
      (fun p : ↥(case1PairSet X t) =>
        (⟨(p : G × G).2, (hmem p).2.2.1, (hmem p).2.2.2.1, hcard2 p⟩ :
          {u : G // u ∉ case1H X t ∧ orderOf u = 2 ∧
            Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) = 2})) ⟨?_, ?_⟩
    · intro p q hpq
      have huv : (p : G × G).2 = (q : G × G).2 := congrArg Subtype.val hpq
      have hp : (p : G × G).1 ∈
          Subgroup.centralizer ({(q : G × G).2} : Set G) ⊓ case1H X t := by
        rw [← huv]
        rw [Subgroup.mem_inf]
        exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hmem p).2.2.2.2, (hmem p).1⟩
      have hq : (q : G × G).1 ∈
          Subgroup.centralizer ({(q : G × G).2} : Set G) ⊓ case1H X t := by
        rw [Subgroup.mem_inf]
        exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hmem q).2.2.2.2, (hmem q).1⟩
      have hp1 : (p : G × G).1 ≠ 1 := by
        intro h1
        have h2 := (hmem p).2.1
        rw [h1, orderOf_one] at h2
        exact absurd h2 (by norm_num)
      have hq1 : (q : G × G).1 ≠ 1 := by
        intro h1
        have h2 := (hmem q).2.1
        rw [h1, orderOf_one] at h2
        exact absurd h2 (by norm_num)
      have h1 : (p : G × G).1 = (q : G × G).1 :=
        eq_of_ne_one_of_card_eq_two (hcard2 q) hp hp1 hq hq1
      exact Subtype.ext (Prod.ext h1 huv)
    · intro u
      obtain ⟨z, hzC0, hz1⟩ := exists_ne_one_of_card_eq_two u.2.2.2
      have hzC : z ∈ (Subgroup.centralizer ({(u : G)} : Set G) ⊓ case1H X t : Subgroup G) :=
        SetLike.mem_coe.mp hzC0
      obtain ⟨hzcent, hzH⟩ := Subgroup.mem_inf.mp hzC
      have hzu : z * (u : G) = (u : G) * z :=
        Subgroup.mem_centralizer_singleton_iff.mp hzcent
      have hordz : orderOf z = 2 := by
        have hdvd : orderOf z ∣
            Nat.card ↥(Subgroup.centralizer ({(u : G)} : Set G) ⊓ case1H X t) :=
          orderOf_dvd_natCard_of_mem hzC
        rw [u.2.2.2] at hdvd
        rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf z) hdvd with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hz1
        · exact h1
      refine ⟨⟨((z, (u : G))), ⟨hzH, hordz, u.2.1, u.2.2.1, hzu⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
  have hU2 : Nat.card
      {u : G // u ∉ case1H X t ∧ orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) = 2} =
      2 * Work.GW2.bCount (case1H X t) 2 :=
    (Nat.card_coe_set_eq ({u : G | u ∉ case1H X t ∧ orderOf u = 2 ∧
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) = 2} : Set G)).trans
      (case1H_U2_card (case1H X t) hcoset)
  have h4a : 4 * Nat.card ↥(case1A X) = 2 * Work.GW2.bCount (case1H X t) 2 := by
    rw [← hPcard, hbij]
    exact hU2
  have hmain : (2 * Nat.card ↥(case1A X)) * 2 = Work.GW2.bCount (case1H X t) 2 * 2 := by
    rw [show (2 * Nat.card ↥(case1A X)) * 2 = 4 * Nat.card ↥(case1A X) from by ring,
      show Work.GW2.bCount (case1H X t) 2 * 2 = 2 * Work.GW2.bCount (case1H X t) 2 from by ring]
    exact h4a
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) hmain).symm

end Work.BSW.Cases.K4
