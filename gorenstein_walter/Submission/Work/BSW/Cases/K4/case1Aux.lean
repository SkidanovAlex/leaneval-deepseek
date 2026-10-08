/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# Bender's Case 1: the group `A⟨t⟩ = C_G(X)⟨t⟩`

Structural part of Bender's §3, Case 1 (`C_G(X) ⊄ N_G(V)`) for a finite group `G` in which the
centralizer of every involution is dihedral of order `8` and all involutions are conjugate
(`Work.BSW.Cases.K4.K4Hyp`), a Klein four-group `V` and a subgroup `X` of order `3` in `N_G(V)`.

Throughout, `A = C_G(X)` and `t` is an involution of `N_G(V) ∩ N_G(X)`.  All the structure needed
for Bender's counting argument is available for the group `H = A⟨t⟩` of order `2|A|`.
-/
import Mathlib
import Submission.Work.BSW.Cases.K4.K4Hyp
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.BSW.Cases.K4.countingFacts

namespace Work.BSW.Cases.K4

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

/-- An odd divisor of `8` is `1`. -/
theorem eq_one_of_dvd_eight_of_odd {n : ℕ} (h : n ∣ 8) (ho : Odd n) : n = 1 := by
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) h
  have h0 : n ≠ 0 := by rintro rfl; norm_num at h
  have h2 : n ≠ 2 := by rintro rfl; norm_num at ho
  have h4 : n ≠ 4 := by rintro rfl; norm_num at ho
  have h8 : n ≠ 8 := by rintro rfl; norm_num at ho
  interval_cases n <;> norm_num at *

/-- A subgroup of order `3` is contained in its own centralizer. -/
theorem le_centralizer_of_card_three {X : Subgroup G} (hX3 : Nat.card ↥X = 3) :
    X ≤ Subgroup.centralizer (X : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsCyclic ↥X := isCyclic_of_prime_card hX3
  exact Subgroup.le_centralizer X

/-! ## The groups `A = C_G(X)` and `H = A⟨t⟩` -/

/-- `A = C_G(X)`. -/
abbrev case1A (X : Subgroup G) : Subgroup G := Subgroup.centralizer (X : Set G)

/-- `H = A⟨t⟩ = C_G(X)⟨t⟩`, the group of order `2 |A|` of Bender's Case 1. -/
abbrev case1H (X : Subgroup G) (t : G) : Subgroup G := case1A X ⊔ Subgroup.zpowers t

/-- A fixed-point-free involution of order `2` normalizing a group `K` inverts it, and `K` is
commutative. -/
theorem comm_and_inverts_of_fixedPointFree {K : Subgroup G} {t : G} (ht2 : t * t = 1)
    (ht : t ∈ Subgroup.normalizer (K : Set G))
    (hfix : ∀ a ∈ K, t * a * t⁻¹ = a → a = 1) :
    (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) ∧ ∀ a ∈ K, t * a * t⁻¹ = a⁻¹ := by
  let φ : ↥K →* ↥K :=
    { toFun := fun x => ⟨t * (x : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht x).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp only [Subgroup.coe_mul]; group }
  have hφcoe : ∀ x : ↥K, ((φ x : ↥K) : G) = t * (x : G) * t⁻¹ := fun x => rfl
  have hinvol : Function.Involutive ⇑φ := by
    intro x
    apply Subtype.ext
    rw [hφcoe, hφcoe]
    rw [show t * (t * (x : G) * t⁻¹) * t⁻¹ =
      (t * t) * (x : G) * (t⁻¹ * t⁻¹) from by group, show t⁻¹ * t⁻¹ = (t * t)⁻¹ from by group,
      ht2, inv_one, mul_one, one_mul]
  have hfp : MonoidHom.FixedPointFree ⇑φ := by
    intro x hx
    apply Subtype.ext
    have h1 : ((φ x : ↥K) : G) = t * (x : G) * t⁻¹ := hφcoe x
    have h2 : ((φ x : ↥K) : G) = (x : G) := congrArg Subtype.val hx
    rw [h1] at h2
    exact hfix x x.2 h2
  have hinv := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfp hinvol
  have hcomm := MonoidHom.FixedPointFree.commute_all_of_involutive hfp hinvol
  constructor
  · intro a ha b hb
    exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩).eq
  · intro a ha
    have h2 := congrArg Subtype.val (congrFun hinv (⟨a, ha⟩ : ↥K))
    rw [hφcoe] at h2
    simpa using h2

section Case1

variable {X : Subgroup G} {t : G}

/-- `t` normalizes `A = C_G(X)` when it normalizes `X`. -/
theorem mem_normalizer_case1A (htN : t ∈ Subgroup.normalizer (X : Set G)) :
    t ∈ Subgroup.normalizer (case1A X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro x hx
    have hx' : t⁻¹ * x * t ∈ (X : Set G) :=
      (Subgroup.mem_normalizer_iff.mp htN (t⁻¹ * x * t)).mpr (by
        have h : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
        rw [h]; exact hx)
    have h := ha (t⁻¹ * x * t) hx'
    calc x * (t * a * t⁻¹) = t * ((t⁻¹ * x * t) * a) * t⁻¹ := by group
      _ = t * (a * (t⁻¹ * x * t)) * t⁻¹ := by rw [h]
      _ = (t * a * t⁻¹) * x := by group
  · intro ha
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro x hx
    have hx' : t * x * t⁻¹ ∈ (X : Set G) := (Subgroup.mem_normalizer_iff.mp htN x).mp hx
    have h := ha (t * x * t⁻¹) hx'
    calc x * a = t⁻¹ * ((t * x * t⁻¹) * (t * a * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * a * t⁻¹) * (t * x * t⁻¹)) * t := by rw [h]
      _ = a * x := by group

/-- `|A|` is odd in the `K4Hyp` setting.  Otherwise `A` contains an involution `u` and
`X ≤ C_G(u)`, of order `8`, would give `3 ∣ 8`. -/
theorem case1A_odd (h : K4Hyp G) (hX3 : Nat.card ↥X = 3) : Odd (Nat.card ↥(case1A X)) := by
  by_contra hodd
  have heven : Even (Nat.card ↥(case1A X)) := Nat.not_odd_iff_even.mp hodd
  rw [even_iff_two_dvd] at heven
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(case1A X)) 2 heven
  have hu2G : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe u]; exact hu2
  have hle : X ≤ cent G (u : G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp u.2) x hx
  have hdvd : Nat.card ↥X ∣ Nat.card ↥(cent G (u : G)) := Subgroup.card_dvd_of_le hle
  rw [h.2.1 (u : G) hu2G, hX3] at hdvd
  exact absurd hdvd (by norm_num)

/-- `t ∉ A` when `|A|` is odd and `t` is an involution. -/
theorem case1t_notMem (ht2 : orderOf t = 2) (hodd : Odd (Nat.card ↥(case1A X))) :
    t ∉ case1A X := by
  intro htA
  have hdvd : orderOf t ∣ Nat.card ↥(case1A X) := orderOf_dvd_natCard_of_mem htA
  rw [ht2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

/-- `C_A(t) = 1` when `|A|` is odd and `t` is an involution: a fixed point of `t` lies in `C_G(t)`
of order `8`, and `A` has odd order. -/
theorem case1A_fixed_trivial (h : K4Hyp G) (hX3 : Nat.card ↥X = 3) (ht2 : orderOf t = 2) :
    ∀ a ∈ case1A X, t * a * t⁻¹ = a → a = 1 := by
  intro a ha hfix
  have hcomm : a * t = t * a := by
    calc a * t = (t * a * t⁻¹) * t := by rw [hfix]
      _ = t * a := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have hmem : a ∈ cent G t := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hdvd8 : orderOf a ∣ 8 := by
    have h1 := orderOf_dvd_natCard_of_mem hmem
    rwa [h.2.1 t ht2] at h1
  have hodd : Odd (Nat.card ↥(case1A X)) := case1A_odd h hX3
  have hodda : Odd (orderOf a) := by
    by_contra hc
    rw [Nat.not_odd_iff_even] at hc
    rw [even_iff_two_dvd] at hc
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (hc.trans (orderOf_dvd_natCard_of_mem ha)))
  exact orderOf_eq_one_iff.mp (eq_one_of_dvd_eight_of_odd hdvd8 hodda)

/-- `A` is commutative and `t` inverts it. -/
theorem case1A_comm_and_inv (h : K4Hyp G) (hX3 : Nat.card ↥X = 3) (ht2 : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (X : Set G)) :
    (∀ a ∈ case1A X, ∀ b ∈ case1A X, a * b = b * a) ∧
      ∀ a ∈ case1A X, t * a * t⁻¹ = a⁻¹ := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  exact comm_and_inverts_of_fixedPointFree htt (mem_normalizer_case1A htN)
    (case1A_fixed_trivial h hX3 ht2)

/-- `A ⊓ ⟨t⟩ = ⊥`. -/
theorem case1A_inf_zpowers (h : K4Hyp G) (hX3 : Nat.card ↥X = 3) (ht2 : orderOf t = 2) :
    case1A X ⊓ Subgroup.zpowers t = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_inf] at hx
  rcases mem_zpowers_eq_one_or ht2 hx.2 with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hx.1) (case1t_notMem ht2 (case1A_odd h hX3))

/-- `|H| = 2 |A|`. -/
theorem case1H_card (h : K4Hyp G) (hX3 : Nat.card ↥X = 3) (ht2 : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (X : Set G)) :
    Nat.card ↥(case1H X t) = 2 * Nat.card ↥(case1A X) := by
  have hN : Subgroup.zpowers t ≤ Subgroup.normalizer (case1A X : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_case1A htN)
  rw [card_sup_of_le_normalizer_of_inf_eq_bot hN (case1A_inf_zpowers h hX3 ht2),
    Nat.card_zpowers, ht2]
  ring

/-- Every element of `H = A⟨t⟩` is in `A` or of the form `a * t`. -/
theorem mem_case1H_iff (ht2 : orderOf t = 2) (htN : t ∈ Subgroup.normalizer (X : Set G))
    {x : G} : x ∈ case1H X t ↔ x ∈ case1A X ∨ ∃ a ∈ case1A X, x = a * t := by
  have hN : Subgroup.zpowers t ≤ Subgroup.normalizer (case1A X : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_case1A htN)
  constructor
  · intro hx
    have hcoe : (↑(case1A X ⊔ Subgroup.zpowers t) : Set G) =
        (case1A X : Set G) * (Subgroup.zpowers t : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN
    have hx' : x ∈ (case1A X : Set G) * (Subgroup.zpowers t : Set G) := by
      rw [← hcoe]; exact hx
    obtain ⟨a, ha, z, hz, haz⟩ := Set.mem_mul.mp hx'
    rcases mem_zpowers_eq_one_or ht2 hz with h1 | h1
    · refine Or.inl ?_
      rw [← haz, h1, mul_one]; exact ha
    · exact Or.inr ⟨a, ha, by rw [← haz, h1]⟩
  · rintro (hx | ⟨a, ha, rfl⟩)
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mul_mem_sup ha (Subgroup.mem_zpowers t)

/-- The involutions of `H = A⟨t⟩` are exactly the elements of `A t`; there are `|A|` of them. -/
theorem case1H_involutions (h : K4Hyp G) (hX3 : Nat.card ↥X = 3) (ht2 : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (X : Set G)) :
    ({x : G | orderOf x = 2 ∧ x ∈ case1H X t} : Set G).ncard = Nat.card ↥(case1A X) := by
  have hcomm := (case1A_comm_and_inv h hX3 ht2 htN).1
  have hinv := (case1A_comm_and_inv h hX3 ht2 htN).2
  have hodd : Odd (Nat.card ↥(case1A X)) := case1A_odd h hX3
  have hset : {x : G | orderOf x = 2 ∧ x ∈ case1H X t} =
      (fun a : G => a * t) '' (case1A X : Set G) := by
    ext x
    constructor
    · rintro ⟨hx2, hxH⟩
      rcases (mem_case1H_iff ht2 htN).mp hxH with hxA | ⟨a, ha, rfl⟩
      · exfalso
        have hd := orderOf_dvd_natCard_of_mem hxA
        rw [hx2] at hd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
      · exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨?_, (mem_case1H_iff ht2 htN).mpr (Or.inr ⟨a, ha, rfl⟩)⟩
      have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      have htat : t * a * t = a⁻¹ := by
        calc t * a * t = t * a * t⁻¹ := by rw [htinv]
          _ = a⁻¹ := hinv a ha
      have hsq : (a * t) * (a * t) = 1 := by
        calc (a * t) * (a * t) = a * (t * a * t) := by group
          _ = a * a⁻¹ := by rw [htat]
          _ = 1 := mul_inv_cancel a
      have hne : a * t ≠ 1 := by
        intro h1
        have h2 : t = a⁻¹ := by
          have := congrArg (fun z => a⁻¹ * z) h1
          simpa [mul_assoc] using this
        exact case1t_notMem ht2 hodd (h2 ▸ (case1A X).inv_mem ha)
      have hd : orderOf (a * t) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf (a * t)) hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact h1
  rw [hset, Set.ncard_image_of_injective (case1A X : Set G)
    (fun a b hab => mul_right_cancel hab)]
  exact (Nat.card_coe_set_eq (case1A X : Set G)).symm

end Case1

end Work.BSW.Cases.K4
