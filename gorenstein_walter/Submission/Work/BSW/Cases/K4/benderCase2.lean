/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# Bender's §3, Case 2: `|G| = 168`

Let `G` be a finite group in which the centralizer of every involution is a non-abelian group of
order `8` containing a Klein four-group and in which all involutions are conjugate
(`Work.BSW.Cases.K4.K4Hyp`).  Let `V` be a Klein four-group, `X ≤ N_G(V)` a subgroup of order `3`
with `C_G(X) ≤ N_G(V)` ("Case 2").  Then `|G| = 168` (`G` is `PSL(2,7)` up to isomorphism).

The base material (Bender's coset/involution count, the structure of `N_G(V)` and of involution
centralizers, and the counting lemmas about `N_G(V)`) lives in
`Submission.Work.BSW.Cases.K4.benderCase2Aux`.
-/
import Mathlib
import Submission.Work.BSW.Cases.K4.benderCase2Aux
import Submission.Work.BSW.Cases.K4.card_conj_mul_card_normalizer
import Submission.Work.BSW.Cases.K4.card_normalizer_le_two_mul_card_centralizer
import Submission.Work.BSW.Cases.K4.normalizer_order_three_le
import Submission.Work.BSW.Cases.K4.not_inverted_of_orderOf_eq_four

namespace Work.BSW.Cases.K4

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

-- @@TARGET-EXTRA@@
/-! ## Coset bound: at most two involutions per non-trivial coset of `N_G(V)` -/

/-- If `u * x * u⁻¹ = x⁻¹` then `u` inverts every power of `x`. -/
theorem conj_zpow_eq_inv {u x : G} (hc : u * x * u⁻¹ = x⁻¹) (k : ℤ) :
    u * x ^ k * u⁻¹ = (x ^ k)⁻¹ := by
  calc u * x ^ k * u⁻¹ = (u * x * u⁻¹) ^ k := by
        simpa [MulAut.conj_apply] using map_zpow (MulAut.conj u).toMonoidHom x k
    _ = (x ^ k)⁻¹ := by rw [hc, inv_zpow]

/-- Nat-exponent version of `conj_zpow_eq_inv`. -/
theorem conj_pow_eq_inv {u x : G} (hc : u * x * u⁻¹ = x⁻¹) (k : ℕ) :
    u * x ^ k * u⁻¹ = (x ^ k)⁻¹ := by
  simpa using conj_zpow_eq_inv hc (k : ℤ)

/-- If `u * x * u = x⁻¹` with `u` an involution, then `u` normalises `⟨x⟩`. -/
theorem mem_normalizer_zpowers_of_mul_eq_inv {u x : G} (hu2 : u * u = 1)
    (hinv : u * x * u = x⁻¹) :
    u ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hc : u * x * u⁻¹ = x⁻¹ := by rw [huinv]; exact hinv
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hk, conj_zpow_eq_inv hc k]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), rfl⟩)
  · intro hz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h3 : u⁻¹ * x ^ m * u = (x ^ m)⁻¹ := by
      simpa [huinv] using conj_zpow_eq_inv hc m
    have hz' : z = (x ^ m)⁻¹ := by
      calc z = u⁻¹ * (u * z * u⁻¹) * u := by group
        _ = u⁻¹ * x ^ m * u := by rw [hm]
        _ = (x ^ m)⁻¹ := h3
    rw [hz']
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), rfl⟩)

/-- An involution `u ∉ N_G(V)` inverts at most two elements of `N_G(V)`. -/
theorem ncard_inverted_le_two (h : K4Hyp G) {V X : Subgroup G} (hV : IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3)
    (hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (V : Set G))
    {u : G} (huH : u ∉ Subgroup.normalizer (V : Set G)) (hu2 : orderOf u = 2) :
    ({x : G | x ∈ Subgroup.normalizer (V : Set G) ∧ u * x * u = x⁻¹} : Set G).ncard ≤ 2 := by
  set H : Subgroup G := Subgroup.normalizer (V : Set G) with hH
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2'
  have hsub : ({x : G | x ∈ H ∧ u * x * u = x⁻¹} : Set G) ⊆
      {1} ∪ ({x : G | orderOf x = 2 ∧ x ∈ cent G u ⊓ H} : Set G) := by
    intro x hx
    obtain ⟨hxH, hxinv⟩ := hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · have hc : u * x * u⁻¹ = x⁻¹ := by rw [huinv]; exact hxinv
      have hdvd24 : orderOf x ∣ 24 := by
        have h' := orderOf_dvd_natCard_of_mem hxH
        rwa [card_normalizer_eq h hV] at h'
      have hx0 : orderOf x ≠ 0 := by
        intro h0
        rw [h0] at hdvd24
        exact absurd hdvd24 (by norm_num)
      have hxord2 : orderOf x = 2 := by
        have hnot3 : ¬ 3 ∣ orderOf x := by
          intro h3
          have hg3 : orderOf (x ^ (orderOf x / 3)) = 3 :=
            orderOf_pow_orderOf_div hx0 h3
          have hgH : x ^ (orderOf x / 3) ∈ H := H.pow_mem hxH _
          have hinv' : u * x ^ (orderOf x / 3) * u = (x ^ (orderOf x / 3))⁻¹ := by
            simpa [huinv] using conj_pow_eq_inv hc (orderOf x / 3)
          have huN := mem_normalizer_zpowers_of_mul_eq_inv hu2' hinv'
          have hcard3 : Nat.card ↥(Subgroup.zpowers (x ^ (orderOf x / 3))) = 3 := by
            rw [Nat.card_zpowers, hg3]
          exact huH (normalizer_order_three_le h hV hXle hX3 hCX
            (Subgroup.zpowers_le.mpr hgH) hcard3 huN)
        have hnot4 : ¬ 4 ∣ orderOf x := by
          intro h4
          have hg4 : orderOf (x ^ (orderOf x / 4)) = 4 :=
            orderOf_pow_orderOf_div hx0 h4
          have hgH : x ^ (orderOf x / 4) ∈ H := H.pow_mem hxH _
          have hinv' : u * x ^ (orderOf x / 4) * u = (x ^ (orderOf x / 4))⁻¹ := by
            simpa [huinv] using conj_pow_eq_inv hc (orderOf x / 4)
          exact not_inverted_of_orderOf_eq_four h hV huH hu2 hgH hg4 hinv'
        have hdvd8 : orderOf x ∣ 8 := by
          have hcop : Nat.Coprime (orderOf x) 3 :=
            (Nat.prime_three.coprime_iff_not_dvd.mpr hnot3).symm
          exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd24)
        obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 3)).mp hdvd8
        interval_cases i
        · exfalso
          have h1 : orderOf x = 1 := by simpa using hni
          exact hx1 (orderOf_eq_one_iff.mp h1)
        · simpa using hni
        · exfalso
          have h4' : orderOf x = 4 := by simpa using hni
          rw [h4'] at hnot4
          exact hnot4 dvd_rfl
        · exfalso
          have h8' : orderOf x = 8 := by simpa using hni
          rw [h8'] at hnot4
          exact hnot4 (by norm_num)
      refine Or.inr ⟨hxord2, ⟨?_, hxH⟩⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h1 : u * x = x⁻¹ * u := by
        calc u * x = (u * x * u) * u := by
              rw [mul_assoc (u * x) u u, hu2', mul_one]
          _ = x⁻¹ * u := by rw [hxinv]
      have h2 : x⁻¹ * u = u * x := by
        simpa [huinv] using congrArg Inv.inv h1
      have hxinv' : x⁻¹ = x := by
        apply inv_eq_of_mul_eq_one_right
        have h2 := pow_orderOf_eq_one x
        rw [hxord2] at h2
        simpa [pow_two] using h2
      calc x * u = x⁻¹ * u := by rw [hxinv']
        _ = u * x := h2
  calc ({x : G | x ∈ H ∧ u * x * u = x⁻¹} : Set G).ncard
      ≤ ({1} ∪ ({x : G | orderOf x = 2 ∧ x ∈ cent G u ⊓ H} : Set G)).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ ({1} : Set G).ncard + ({x : G | orderOf x = 2 ∧ x ∈ cent G u ⊓ H} : Set G).ncard :=
        Set.ncard_union_le _ _
    _ ≤ 1 + 1 := by
        rw [Set.ncard_singleton]
        exact Nat.add_le_add_left (card_involutions_cent_inf_normalizer_le_one h hV huH hu2) 1
    _ = 2 := by norm_num

/-- A coset `z·N_G(V)` with `z ∉ N_G(V)` an involution contains at most two involutions. -/
theorem ncard_involutions_mul_coset_le_two (h : K4Hyp G) {V X : Subgroup G} (hV : IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3)
    (hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (V : Set G)) {z : G}
    (hzH : z ∉ Subgroup.normalizer (V : Set G)) (hz2 : orderOf z = 2) :
    ({y : G | orderOf y = 2 ∧ ∃ x ∈ Subgroup.normalizer (V : Set G), y = z * x} : Set G).ncard
      ≤ 2 := by
  set H : Subgroup G := Subgroup.normalizer (V : Set G) with hH
  have hset : ({y : G | orderOf y = 2 ∧ ∃ x ∈ H, y = z * x} : Set G)
      = (fun x : G => z * x) '' ({x : G | x ∈ H ∧ z * x * z = x⁻¹} : Set G) := by
    ext y
    constructor
    · rintro ⟨hy2, x, hxH, rfl⟩
      refine ⟨x, ⟨hxH, ?_⟩, rfl⟩
      have hsq : (z * x) ^ 2 = 1 := (orderOf_eq_prime_iff.mp hy2).1
      have hsq' : (z * x) * (z * x) = 1 := by simpa [pow_two] using hsq
      have hmain := congrArg (fun t : G => t * x⁻¹) hsq'
      simpa [mul_assoc] using hmain
    · rintro ⟨x, ⟨hxH, hconj⟩, rfl⟩
      refine ⟨?_, x, hxH, rfl⟩
      apply orderOf_eq_prime_iff.mpr
      refine ⟨?_, ?_⟩
      · rw [pow_two]
        calc (z * x) * (z * x) = (z * x * z) * x := by group
          _ = x⁻¹ * x := by rw [hconj]
          _ = 1 := inv_mul_cancel x
      · intro h1
        have h1' : z * x = 1 := h1
        have h3 : z = x⁻¹ := by
          have h4 : z = (z * x) * x⁻¹ := by group
          rw [h1', one_mul] at h4
          exact h4
        exact hzH (by rw [h3]; exact H.inv_mem hxH)
  rw [hset, Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)]
  exact ncard_inverted_le_two h hV hXle hX3 hCX hzH hz2

/-- The number of involutions outside `N_G(V)` is at most twice the number of non-trivial cosets of
`N_G(V)`: each such coset contains at most two involutions. -/
theorem ncard_involutions_not_mem_normalizer_le (h : K4Hyp G) {V X : Subgroup G} (hV : IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3)
    (hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    ({x : G | orderOf x = 2 ∧ x ∉ Subgroup.normalizer (V : Set G)} : Set G).ncard
      ≤ 2 * ((Subgroup.normalizer (V : Set G)).index - 1) := by
  set H : Subgroup G := Subgroup.normalizer (V : Set G) with hH
  let S : Type := {x : G // orderOf x = 2 ∧ x ∉ H}
  let β : Type := {c : G ⧸ H // c ≠ QuotientGroup.mk 1}
  let f : S → β := fun x => ⟨QuotientGroup.mk x.1, by
      intro hcon
      have h1 : (x.1)⁻¹ * (1 : G) ∈ H := QuotientGroup.eq.mp hcon
      have h2 : x.1 ∈ H := by simpa using H.inv_mem h1
      exact x.2.2 h2⟩
  have hmap : ∀ (x : S) (c : β), f x = c ↔ (QuotientGroup.mk x.1 : G ⧸ H) = c.1 := by
    intro x c
    constructor
    · intro hh; rw [← hh]
    · intro hh; exact Subtype.ext hh
  have hfiber : ∀ c : β, Nat.card {x : S | f x = c} ≤ 2 := by
    intro c
    let F : Set G := {x : G | orderOf x = 2 ∧ x ∉ H ∧ (QuotientGroup.mk x : G ⧸ H) = c.1}
    have hcardF : Nat.card {x : S | f x = c} = F.ncard := by
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_congr
        { toFun := fun x => (⟨x.1.1, x.1.2.1, x.1.2.2, (hmap x.1 c).mp x.2⟩ : F)
          invFun := fun y => (⟨⟨y.1, y.2.1, y.2.2.1⟩,
            (hmap ⟨y.1, y.2.1, y.2.2.1⟩ c).mpr y.2.2.2⟩ : {x : S | f x = c})
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    by_cases hempty : ∃ z : S, f z = c
    · obtain ⟨z, hz⟩ := hempty
      have hz2 : orderOf (z.1 : G) = 2 := z.2.1
      have hzH : (z.1 : G) ∉ H := z.2.2
      have hsub : F ⊆ ({y : G | orderOf y = 2 ∧ ∃ x ∈ H, y = z.1 * x} : Set G) := by
        rintro y ⟨hy2, hyH, hymk⟩
        refine ⟨hy2, ?_⟩
        have h1 : y⁻¹ * z.1 ∈ H := by
          have hh : (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk z.1 := by
            rw [hymk, (hmap z c).mp hz]
          exact QuotientGroup.eq.mp hh
        exact ⟨(y⁻¹ * z.1)⁻¹, H.inv_mem h1, by group⟩
      calc Nat.card {x : S | f x = c} = F.ncard := hcardF
        _ ≤ ({y : G | orderOf y = 2 ∧ ∃ x ∈ H, y = z.1 * x} : Set G).ncard :=
            Set.ncard_le_ncard hsub
        _ ≤ 2 := ncard_involutions_mul_coset_le_two h hV hXle hX3 hCX hzH hz2
    · have hFempty : F = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨y, hy⟩
        exact hempty ⟨⟨y, hy.1, hy.2.1⟩, (hmap ⟨y, hy.1, hy.2.1⟩ c).mpr hy.2.2⟩
      rw [hcardF, hFempty, Set.ncard_empty]
      norm_num
  have hmain := card_le_mul_card_of_fibers_le f 2 hfiber
  have hβ : Nat.card β = H.index - 1 := by
    have h1 : Nat.card β = ({c : G ⧸ H | c ≠ QuotientGroup.mk 1} : Set (G ⧸ H)).ncard :=
      Nat.card_coe_set_eq _
    rw [h1]
    have h2 : ({c : G ⧸ H | c ≠ QuotientGroup.mk 1} : Set (G ⧸ H))
        = (Set.univ : Set (G ⧸ H)) \ {QuotientGroup.mk 1} := by
      ext c
      simp
    rw [h2, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
    rfl
  have hS : Nat.card S = ({x : G | orderOf x = 2 ∧ x ∉ H} : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [hS, hβ] at hmain
  calc ({x : G | orderOf x = 2 ∧ x ∉ H} : Set G).ncard
      ≤ (H.index - 1) * 2 := hmain
    _ = 2 * (H.index - 1) := Nat.mul_comm _ _

/-- Bender's §3, Case 2: if `C_G(X) ≤ N_G(V)` for a subgroup `X ≤ N_G(V)` of order `3` then
`|G| = 168` (`G` is `PSL(2,7)` up to isomorphism). -/
theorem benderCase2 {G : Type} [Group G] [Finite G] (h : Work.BSW.Cases.K4.K4Hyp G)
    (V X : Subgroup G) (hV : Work.BSW.Cases.K4.IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3)
    (hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card G = 168 := by
  set H : Subgroup G := Subgroup.normalizer (V : Set G) with hH
  obtain ⟨t, ht⟩ := h.1
  have hI8 : ({x : G | orderOf x = 2} : Set G).ncard * 8 = Nat.card G :=
    card_involutions_mul_eight h ht
  have h9 : ({x : G | orderOf x = 2 ∧ x ∈ H} : Set G).ncard = 9 :=
    card_involutions_normalizer h hV
  have h24 : Nat.card ↥H = 24 := card_normalizer_eq h hV
  have hsplit : ({x : G | orderOf x = 2} : Set G).ncard =
      ({x : G | orderOf x = 2 ∧ x ∈ H} : Set G).ncard +
        ({x : G | orderOf x = 2 ∧ x ∉ H} : Set G).ncard := by
    have hunion : ({x : G | orderOf x = 2 ∧ x ∈ H} : Set G) ∪
        {x : G | orderOf x = 2 ∧ x ∉ H} = {x : G | orderOf x = 2} := by
      ext x
      simp only [Set.mem_union, Set.mem_setOf_eq]
      tauto
    have hdisj : Disjoint ({x : G | orderOf x = 2 ∧ x ∈ H} : Set G)
        {x : G | orderOf x = 2 ∧ x ∉ H} := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hx'.2 hx.2
    rw [← hunion, Set.ncard_union_eq hdisj]
  have hub : ({x : G | orderOf x = 2 ∧ x ∉ H} : Set G).ncard ≤ 2 * (H.index - 1) :=
    ncard_involutions_not_mem_normalizer_le h hV hXle hX3 hCX
  have hlb : 12 ≤ ({x : G | orderOf x = 2 ∧ x ∉ H} : Set G).ncard :=
    twelve_le_ncard_involutions_not_mem_normalizer h hV
  have hidx : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
  set b : ℕ := ({x : G | orderOf x = 2 ∧ x ∉ H} : Set G).ncard with hb
  set k : ℕ := H.index with hk
  set n : ℕ := Nat.card G with hn
  have h1 : n = 8 * (9 + b) := by
    have hh := hI8
    rw [hsplit, h9] at hh
    omega
  have h2 : n = 24 * k := by
    have hh := hidx
    rw [h24] at hh
    omega
  have h3 : b ≤ 2 * (k - 1) := hub
  have h4 : 12 ≤ b := hlb
  omega

end Work.BSW.Cases.K4
