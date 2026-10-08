/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# Bender's §3, Case 2: `|G| = 168`

Bender, *Finite groups with large subgroups*, Illinois J. Math. **18** (1974) 223–228, §3.
Let `G` be a finite group in which the centralizer of every involution is a non-abelian group of
order `8` containing a Klein four-group and in which all involutions are conjugate
(`Work.BSW.Cases.K4.K4Hyp`).  Let `V` be a Klein four-group, `X ≤ N_G(V)` a subgroup of order `3`
with `C_G(X) ≤ N_G(V)` ("Case 2").  Then `|G| = 168` (`G` is `PSL(2,7)` up to isomorphism).

The proof follows Bender's counting argument with `H = N_G(V)` (order `24`, containing exactly
`9` involutions): every nontrivial coset of `H` contains at most two involutions, and the six
involutions of `H ∖ V` show that there are at least six cosets with exactly two involutions.  The
two inequalities `|G| ≤ 168 ≤ |G|` are then pure arithmetic.

The key point where the hypothesis `C_G(X) ≤ N_G(V)` enters is `N_G(Y) ≤ N_G(V)` for every
subgroup `Y ≤ N_G(V)` of order `3` (Bender's "`N_G(X) = N_G(V)`"), which is used to show that
`N_G(V) ∩ wN_G(V)w⁻¹` is elementary abelian for every involution `w ∉ N_G(V)`; consequently `w`
inverts at most two elements of `N_G(V)`.
-/
import Mathlib
import Submission.Work.BSW.Cases.K4.K4Hyp
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.BSW.Cases.K4.fourGroupNormalizer
import Submission.Work.BSW.Cases.K4.card_involutions_of_card_eight
import Submission.Work.BSW.Cases.K4.ncard_involutions_coset_eq

namespace Work.BSW.Cases.K4

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

/-! ## Two elementary counting lemmas -/

/-- `|A ⊔ B| * |A ⊓ B| = |A| * |B|` for subgroups `A`, `B` with `B ≤ N_G(A)` (equivalently
`AB = BA` is a subgroup).  This is the cardinality shadow of the second isomorphism theorem. -/
theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAB : (A ⊓ B).subgroupOf B = A.subgroupOf B := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have h1 : (A.subgroupOf B).index * Nat.card ↥(A ⊓ B) = Nat.card ↥B := by
    have hc : Nat.card ↥(A.subgroupOf B) = Nat.card ↥(A ⊓ B) := by
      rw [← hAB]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ B ≤ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf B)
  have h2 : (A.subgroupOf (A ⊔ B)).index * Nat.card ↥A = Nat.card ↥(A ⊔ B) := by
    have hc : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf (A ⊔ B))
  have hidx : (A.subgroupOf B).index = (A.subgroupOf (A ⊔ B)).index := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer h
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A h
    rw [Subgroup.index_eq_card (A.subgroupOf B),
      Subgroup.index_eq_card (A.subgroupOf (A ⊔ B)), sup_comm]
    exact Nat.card_congr e.toEquiv
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = ((A.subgroupOf (A ⊔ B)).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [h2]
    _ = ((A.subgroupOf B).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [hidx]
    _ = Nat.card ↥A * ((A.subgroupOf B).index * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h1]

/-- The number of involutions of a `K4`-group is `|G| / 8`. -/
theorem card_involutions_mul_eight (h : K4Hyp G) {t : G} (ht : orderOf t = 2) :
    {x : G | orderOf x = 2}.ncard * 8 = Nat.card G := by
  have hconj : {x : G | orderOf x = 2} = conjugatesOf t := by
    ext x
    rw [conjugatesOf, Set.mem_setOf_eq]
    constructor
    · intro hx
      exact (h.2.2.2.2 t x ht hx)
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  rw [hconj, ← Subgroup.index_centralizer_eq_ncard t, ← h.2.1 t ht]
  exact Subgroup.index_mul_card _

/-- The involutions of a four-group. -/
theorem IsV4.ncard_involutions {W : Subgroup G} (hW : IsV4 W) :
    {x : G | orderOf x = 2 ∧ x ∈ W}.ncard = 3 := by
  have hset : {x : G | orderOf x = 2 ∧ x ∈ W} = (W : Set G) \ {1} := by
    ext x
    constructor
    · rintro ⟨hx, hxW⟩
      exact ⟨hxW, by rintro rfl; simp at hx⟩
    · rintro ⟨hxW, hx1⟩
      refine ⟨?_, hxW⟩
      rw [orderOf_eq_prime_iff]
      exact ⟨by rw [pow_two]; exact hW.2 x hxW, hx1⟩
  rw [hset, Set.ncard_sdiff_singleton_of_mem (W.one_mem),
    show (W : Set G).ncard = 4 from by rw [← Nat.card_coe_set_eq]; exact hW.1]

/-- The elements of `⟨u⟩` for an involution `u` are `1` and `u`. -/
theorem zpowers_eq_pair_of_sq_eq_one {u : G} (hu : u * u = 1) :
    (Subgroup.zpowers u : Set G) = {1, u} := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : u ^ k = u ^ (k % (2 : ℤ)) := zpow_eq_zpow_emod' k (by rw [pow_two]; exact hu)
    rw [h1]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [hk, zpow_zero]; simp
    · rw [hk, zpow_one]; simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers u

/-- The elements of `⟨u⟩` for an involution `u`. -/
theorem mem_zpowers_pair_of_sq_eq_one {u y : G} (hu : u * u = 1)
    (hy : y ∈ Subgroup.zpowers u) : y = 1 ∨ y = u := by
  have h : y ∈ ({1, u} : Set G) := by
    rw [← zpowers_eq_pair_of_sq_eq_one hu]
    exact hy
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

/-- The involutions in the coset `W * u` of a four-group `W` by an involution `u ∉ W` normalizing
it are in bijection with `C_W(u)`; in particular they number `|C_W(u)|`. -/
theorem ncard_involutions_coset_mul_eq {W : Subgroup G} (hW : IsV4 W) {u : G}
    (huN : u ∈ Subgroup.normalizer (W : Set G)) (huW : u ∉ W) (hu2 : orderOf u = 2) :
    {x : G | orderOf x = 2 ∧ ∃ w ∈ W, x = w * u}.ncard =
      Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) := by
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have key : ({x : G | orderOf x = 2 ∧ ∃ w ∈ W, x = w * u} : Set G).ncard =
      ((W ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G).ncard := by
    refine Set.ncard_congr (fun x _ => x * u) ?_ ?_ ?_
    · rintro x ⟨hx2, w, hwW, rfl⟩
      have hsq : (w * u) * (w * u) = 1 := by
        have h := (orderOf_eq_prime_iff.mp hx2).1
        rwa [pow_two] at h
      have h1 : (w * u) * (w * u) = w * (u * w * u) := by group
      have h2 : w * (u * w * u) = 1 := by rw [← h1]; exact hsq
      have h3 : u * w * u = w := by
        have h4 : w⁻¹ * (w * (u * w * u)) = w⁻¹ * 1 := by rw [h2]
        have h5 : u * w * u = w⁻¹ := by simpa [mul_assoc] using h4
        rwa [inv_eq_of_mul_eq_one_left (hW.2 w hwW)] at h5
      have hcomm : w * u = u * w := by
        calc w * u = (u * w * u) * u := by rw [h3]
          _ = u * w * (u * u) := by group
          _ = u * w := by rw [hu2', mul_one]
      refine ⟨?_, ?_⟩
      · show w * u * u ∈ W
        rw [mul_assoc, hu2', mul_one]
        exact hwW
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        show w * u * u * u = u * (w * u * u)
        rw [mul_assoc, hu2', mul_one, mul_assoc, hu2', mul_one]
        exact hcomm
    · intro a b _ _ hab
      exact mul_right_cancel hab
    · rintro y ⟨hyW, hyC⟩
      refine ⟨y * u, ⟨?_, y, hyW, rfl⟩, ?_⟩
      · have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
        rw [orderOf_eq_prime_iff]
        refine ⟨?_, ?_⟩
        · rw [pow_two]
          calc (y * u) * (y * u) = y * (u * y) * u := by group
            _ = y * (y * u) * u := by rw [← hyu]
            _ = (y * y) * (u * u) := by group
            _ = 1 := by rw [hW.2 y hyW, hu2', mul_one]
        · intro h1
          refine huW ?_
          have h2 : y = u⁻¹ := mul_eq_one_iff_eq_inv.mp h1
          rw [show u⁻¹ = u from inv_eq_of_mul_eq_one_left hu2'] at h2
          rw [← h2]
          exact hyW
      · show y * u * u = y
        rw [mul_assoc, hu2', mul_one]
  rw [key]
  exact (Nat.card_coe_set_eq _).symm

/-- For an involution `u` normalizing a four-group `W` with `u ∉ W`, the centralizer of `u` in
`W` has order `2`. -/
theorem card_centralizer_inf_of_isV4 (h : K4Hyp G) {W : Subgroup G} (hW : IsV4 W) {u : G}
    (huN : u ∈ Subgroup.normalizer (W : Set G)) (huW : u ∉ W) (hu2 : orderOf u = 2) :
    Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) = 2 := by
  classical
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have hzN : Subgroup.zpowers u ≤ Subgroup.normalizer (W : Set G) := Subgroup.zpowers_le.mpr huN
  have hzcard : Nat.card ↥(Subgroup.zpowers u) = 2 := by rw [Nat.card_zpowers, hu2]
  have hinfbot : W ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzW, hzu⟩ := hz
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_pair_of_sq_eq_one hu2' hzu with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hzW) huW
  have hWcard : Nat.card ↥W = 4 := hW.1
  have hTcard : Nat.card ↥(W ⊔ Subgroup.zpowers u) = 8 := by
    rw [card_sup_of_le_normalizer_of_inf_eq_bot hzN hinfbot, hWcard, hzcard]
  have hTnab : ¬ IsMulCommutative ↥(W ⊔ Subgroup.zpowers u) := by
    intro hc
    have hcent : u ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyT : y ∈ (W ⊔ Subgroup.zpowers u : Subgroup G) := Subgroup.mem_sup_left hy
      have huT : u ∈ (W ⊔ Subgroup.zpowers u : Subgroup G) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
      have hcomm := isMulCommutative_iff.mp hc (⟨y, hyT⟩ : ↥(W ⊔ Subgroup.zpowers u))
        (⟨u, huT⟩ : ↥(W ⊔ Subgroup.zpowers u))
      have := congrArg Subtype.val hcomm
      simpa using this
    rw [centralizer_eq_self_of_isV4 h hW] at hcent
    exact huW hcent
  have hzcard' : Nat.card ↥(Subgroup.zpowers u) = 2 := hzcard
  set T : Subgroup G := W ⊔ Subgroup.zpowers u with hT
  have hTcard' : Nat.card ↥T = 8 := hTcard
  have hTnab' : ¬ IsMulCommutative ↥T := hTnab
  have h5 : Nat.card {x : ↥T | orderOf x = 2} = 5 :=
    card_involutions_of_card_eight hTcard' hTnab' (W.subgroupOf T)
      (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : W ≤ T)).toEquiv]
        exact hWcard)
      (by
        intro w hw
        rw [Subgroup.mem_subgroupOf] at hw
        exact Subtype.ext (hW.2 w hw))
  have hTinv5 : ({x : G | orderOf x = 2 ∧ x ∈ T} : Set G).ncard = 5 := by
    rw [← Nat.card_coe_set_eq, ← h5]
    exact Nat.card_congr {
      toFun := fun x => ⟨⟨x.1, x.2.2⟩, by
        show orderOf (⟨x.1, x.2.2⟩ : ↥T) = 2
        rw [← Subgroup.orderOf_coe]
        exact x.2.1⟩
      invFun := fun y => ⟨y.1.1, by
        refine ⟨?_, y.1.2⟩
        show orderOf ((y.1 : ↥T) : G) = 2
        rw [Subgroup.orderOf_coe]
        exact y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hTmem : ∀ x : G, x ∈ T ↔ x ∈ W ∨ ∃ w ∈ W, x = w * u := by
    intro x
    have hcoe : (↑T : Set G) = (W : Set G) * (Subgroup.zpowers u : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left W (Subgroup.zpowers u) hzN
    constructor
    · intro hx
      have hx' : x ∈ (W : Set G) * (Subgroup.zpowers u : Set G) := by
        rw [← hcoe]
        exact hx
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx'
      rcases mem_zpowers_pair_of_sq_eq_one hu2' hb with hb1 | hb1
      · refine Or.inl ?_
        rw [hb1, mul_one] at hab
        rwa [hab] at ha
      · exact Or.inr ⟨a, ha, by rw [← hab, hb1]⟩
    · rintro (hx | ⟨w, hw, rfl⟩)
      · exact Subgroup.mem_sup_left hx
      · exact Subgroup.mul_mem_sup hw (Subgroup.mem_zpowers u)
  have hdisj : Disjoint (W : Set G) {x : G | ∃ w ∈ W, x = w * u} := by
    rw [Set.disjoint_left]
    rintro x hxW ⟨w, hw, rfl⟩
    refine huW ?_
    have h1 : u = w⁻¹ * (w * u) := by group
    rw [h1]
    exact W.mul_mem (W.inv_mem hw) hxW
  have hsplit : ({x : G | orderOf x = 2 ∧ x ∈ T} : Set G) =
      {x : G | orderOf x = 2 ∧ x ∈ W} ∪ {x : G | orderOf x = 2 ∧ ∃ w ∈ W, x = w * u} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [hTmem x]
    tauto
  have hdisj' : Disjoint {x : G | orderOf x = 2 ∧ x ∈ W}
      {x : G | orderOf x = 2 ∧ ∃ w ∈ W, x = w * u} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.mp hdisj hx.2 hx'.2
  have hcount : ({x : G | orderOf x = 2 ∧ x ∈ T} : Set G).ncard =
      ({x : G | orderOf x = 2 ∧ x ∈ W} : Set G).ncard +
      ({x : G | orderOf x = 2 ∧ ∃ w ∈ W, x = w * u} : Set G).ncard := by
    rw [hsplit, Set.ncard_union_eq hdisj']
  set N : ℕ := Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) with hN
  have hsum : 3 + N = 5 := by
    rw [hcount, hW.ncard_involutions, ncard_involutions_coset_mul_eq hW huN huW hu2, ← hN] at hTinv5
    exact hTinv5
  rw [hN]
  omega

/-- Two distinct commuting involutions generate a four-group. -/
theorem isV4_zpowers_sup_zpowers {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (hab : a * b = b * a) :
    IsV4 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  have haord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hbord : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb) hb1
  have haz : Nat.card ↥(Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, haord]
  have hbz : Nat.card ↥(Subgroup.zpowers b) = 2 := by rw [Nat.card_zpowers, hbord]
  have hsq_a : ∀ y ∈ Subgroup.zpowers a, y * y = 1 := by
    intro y hy
    rcases mem_zpowers_pair_of_sq_eq_one ha hy with h | h
    · rw [h]; simp
    · rw [h]; exact ha
  have hsq_b : ∀ y ∈ Subgroup.zpowers b, y * y = 1 := by
    intro y hy
    rcases mem_zpowers_pair_of_sq_eq_one hb hy with h | h
    · rw [h]; simp
    · rw [h]; exact hb
  have hcomm : ∀ y ∈ Subgroup.zpowers a, ∀ z ∈ Subgroup.zpowers b, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((show Commute a b from hab).zpow_zpow i j).eq
  have hzN : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy z hz
    rw [show y * z * y⁻¹ = z from by
      have hc : y * z = z * y := (hcomm z hz y hy).symm
      rw [hc]; group]
    exact hz
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_pair_of_sq_eq_one ha hy1 with h | h
    · exact h
    · rcases mem_zpowers_pair_of_sq_eq_one hb hy2 with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hne
  refine ⟨?_, ?_⟩
  · rw [card_sup_of_le_normalizer_of_inf_eq_bot hzN hinf, haz, hbz]
  · have hcoe : (↑(Subgroup.zpowers a ⊔ Subgroup.zpowers b) : Set G) =
        (Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN
    intro y hy
    have hy' : y ∈ (Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G) := by
      rw [← hcoe]
      exact hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy'
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [hcomm u hu v hv]
      _ = u * u * (v * v) := by group
      _ = 1 := by rw [hsq_a u hu, hsq_b v hv]; simp

/-- An element of order `4` of `N_G(W)` has its square in `W`. -/
theorem sq_mem_of_orderOf_eq_four_of_mem_normalizer (h : K4Hyp G) {W : Subgroup G}
    (hW : IsV4 W) {x : G} (hxN : x ∈ Subgroup.normalizer (W : Set G)) (hx4 : orderOf x = 4) :
    x * x ∈ W := by
  have hWcard : Nat.card ↥W = 4 := hW.1
  have hNcard : Nat.card ↥(Subgroup.normalizer (W : Set G)) = 24 := card_normalizer_eq h hW
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (W : Set G) := Subgroup.zpowers_le.mpr hxN
  have hzcard : Nat.card ↥(Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hx4]
  have hxW : x ∉ W := by
    intro hxw
    have h' : orderOf x ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hW.2 x hxw
    rw [hx4] at h'
    norm_num at h' 
  set n : ℕ := Nat.card ↥(W ⊓ Subgroup.zpowers x) with hn
  set m : ℕ := Nat.card ↥(W ⊔ Subgroup.zpowers x) with hm
  have hmul : m * n = 4 * 4 := by
    have h' := card_sup_mul_card_inf_of_le_normalizer hzN
    rw [hWcard, hzcard] at h'
    simpa [hn, hm] using h'
  have hdvdm : m ∣ 24 := by
    have hle : W ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (W : Set G) :=
      sup_le Subgroup.le_normalizer hzN
    have h' := Subgroup.card_dvd_of_le hle
    rwa [hNcard, ← hm] at h'
  have hdvdn : n ∣ 4 := by
    have h' := Subgroup.card_dvd_of_le (inf_le_right : W ⊓ Subgroup.zpowers x ≤ Subgroup.zpowers x)
    rwa [hzcard, ← hn] at h'
  have hn2 : n = 2 := by
    obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp hdvdn
    interval_cases i
    · exfalso
      have hn1 : n = 1 := by simpa using hni
      rw [hn1, mul_one] at hmul
      norm_num at hmul
      obtain ⟨k, hk⟩ := hdvdm
      rw [hmul] at hk
      omega
    · simpa using hni
    · exfalso
      have hn4 : n = 4 := by simpa using hni
      have heq : W ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [← hn, hn4, hzcard])
      have hmem : x ∈ W ⊓ Subgroup.zpowers x := by rw [heq]; exact Subgroup.mem_zpowers x
      exact hxW hmem.1
  have hm8 : m = 8 := by
    rw [hn2] at hmul
    norm_num at hmul
    omega
  have hidx : (W.subgroupOf (W ⊔ Subgroup.zpowers x)).index = 2 := by
    rw [Subgroup.index_eq_card_div, ← hm, hm8]
    have h4 : Nat.card ↥(W.subgroupOf (W ⊔ Subgroup.zpowers x)) = 4 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (le_sup_left : W ≤ W ⊔ Subgroup.zpowers x)).toEquiv).trans hWcard
    rw [h4]
  have hxT : x ∈ (W ⊔ Subgroup.zpowers x : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hmem : (⟨x, hxT⟩ : ↥(W ⊔ Subgroup.zpowers x)) * ⟨x, hxT⟩ ∈
      W.subgroupOf (W ⊔ Subgroup.zpowers x) := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

/-- `C_G(u) ⊓ N_G(W)` is a four-group for an involution `u ∈ N_G(W) ∖ W`. -/
theorem isV4_centralizer_inf_normalizer (h : K4Hyp G) {W : Subgroup G} (hW : IsV4 W) {u : G}
    (huN : u ∈ Subgroup.normalizer (W : Set G)) (huW : u ∉ W) (hu2 : orderOf u = 2) :
    IsV4 (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.normalizer (W : Set G)) := by
  have hNcard : Nat.card ↥(Subgroup.normalizer (W : Set G)) = 24 := card_normalizer_eq h hW
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have hcard : Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) = 2 :=
    card_centralizer_inf_of_isV4 h hW huN huW hu2
  obtain ⟨z, hz2⟩ : ∃ z : ↥(W ⊓ Subgroup.centralizer ({u} : Set G)), z ≠ 1 := by
    haveI hnt : Nontrivial ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) := by
      haveI := Fintype.ofFinite ↥(W ⊓ Subgroup.centralizer ({u} : Set G))
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcard]
      norm_num
    exact ⟨Classical.choose (exists_ne (1 : ↥(W ⊓ Subgroup.centralizer ({u} : Set G)))),
      Classical.choose_spec (exists_ne (1 : ↥(W ⊓ Subgroup.centralizer ({u} : Set G))))⟩
  obtain ⟨hvW, hvC⟩ := z.2
  have hv1 : (z : G) ≠ 1 := by rintro h1; exact hz2 (Subtype.ext h1)
  have hv2 : (z : G) * (z : G) = 1 := hW.2 (z : G) hvW
  have hvu : (z : G) * u = u * (z : G) := Subgroup.mem_centralizer_singleton_iff.mp hvC
  have hune : u ≠ (z : G) := fun h1 => huW (h1 ▸ hvW)
  have hV4gen : IsV4 (Subgroup.zpowers (z : G) ⊔ Subgroup.zpowers u) :=
    isV4_zpowers_sup_zpowers hv2 hu2' hv1 (by rintro rfl; simp at hu2) (fun h1 => hune h1.symm) hvu
  set G0 : Subgroup G := Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.normalizer (W : Set G) with hG0
  have hle : Subgroup.zpowers (z : G) ⊔ Subgroup.zpowers u ≤ G0 := by
    rw [hG0]
    refine sup_le ?_ ?_
    · refine le_inf (Subgroup.zpowers_le.mpr hvC) ?_
      exact Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hvW)
    · refine le_inf (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) ?_
      exact Subgroup.zpowers_le.mpr huN
  have hge : 4 ≤ Nat.card ↥G0 := by
    have h' := Subgroup.card_dvd_of_le hle
    rw [hV4gen.1] at h'
    exact Nat.le_of_dvd Nat.card_pos h'
  have hdvd : Nat.card ↥G0 ∣ 8 := by
    have h' : Nat.card ↥G0 ∣ Nat.card ↥(Subgroup.centralizer ({u} : Set G)) :=
      Subgroup.card_dvd_of_le (by rw [hG0]; exact inf_le_left)
    rwa [h.2.1 u hu2] at h'
  have hne8 : Nat.card ↥G0 ≠ 8 := by
    intro h8
    have hinf : G0 = Subgroup.centralizer ({u} : Set G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h.2.1 u hu2])
    have hle' : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (W : Set G) := by
      rw [← hinf]; exact inf_le_right
    have hmul := card_sup_mul_card_inf_of_le_normalizer hle'
    set m : ℕ := Nat.card ↥(W ⊔ Subgroup.centralizer ({u} : Set G)) with hm
    have h16 : m = 16 := by
      have h1 : Nat.card ↥W = 4 := hW.1
      have h2 : Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 8 := h.2.1 u hu2
      have h3 : Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) = 2 := hcard
      rw [h1, h2, h3] at hmul
      norm_num at hmul
      omega
    have hdvd' : m ∣ 24 := by
      have h'' := Subgroup.card_dvd_of_le (sup_le Subgroup.le_normalizer hle')
      rwa [hNcard, ← hm] at h''
    obtain ⟨k, hk⟩ := hdvd'
    rw [h16] at hk
    omega
  have hcard4 : Nat.card ↥G0 = 4 := by
    obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 3)).mp hdvd
    interval_cases i
    · exfalso; omega
    · exfalso; omega
    · exact hni
    · exact absurd hni hne8
  have heq : Subgroup.zpowers (z : G) ⊔ Subgroup.zpowers u = G0 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard4, hV4gen.1])
  rw [← heq]
  exact hV4gen

/-! ## Counting lemmas -/

/-- If every fiber of `f : α → β` has at most `k` elements then `|α| ≤ |β| * k`. -/
theorem card_le_mul_card_of_fibers_le {α β : Type*} [Finite α] [Finite β] (f : α → β) (k : ℕ)
    (h : ∀ b, Nat.card {a : α | f a = b} ≤ k) : Nat.card α ≤ Nat.card β * k := by
  letI := Fintype.ofFinite β
  calc Nat.card α = Nat.card ((y : β) × {x : α // f x = y}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ b : β, Nat.card {a : α // f a = b} := Nat.card_sigma
    _ ≤ ∑ _b : β, k := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card β * k := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]

/-! ## The Case-2 hypothesis: normalizers of subgroups of order `3` -/

/-- No involution of a `K4`-group commutes with an element of order `3` (otherwise the order-`3`
element would lie in an involution centralizer of order `8`). -/
theorem not_commute_of_orderOf_eq_three (h : K4Hyp G) {z x : G} (hz : orderOf z = 2)
    (hx : orderOf x = 3) : ¬ (z * x = x * z) := by
  intro hc
  have hcomm : Commute z x := hc
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({z} : Set G) := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm.zpow_right k).eq.symm
  have hdvd : 3 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) := by
    have h' := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hx] at h'
  rw [h.2.1 z hz] at hdvd
  omega

-- @@BEGIN-MY-EXTRA@@
/-! ## Involutions of a subgroup and of an involution centralizer -/

/-- The involutions of a subgroup `S`, counted as elements of the ambient group. -/
theorem ncard_involutions_subgroup (S : Subgroup G) :
    ({x : G | orderOf x = 2 ∧ x ∈ S} : Set G).ncard = Nat.card {x : ↥S | orderOf x = 2} := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.2⟩, (Subgroup.orderOf_mk x.1 x.2.2).trans x.2.1⟩
      invFun := fun y => ⟨y.1.1, (Subgroup.orderOf_coe y.1).trans y.2, y.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

/-- An involution centralizer in the `K4` setting contains exactly five involutions. -/
theorem card_involutions_cent_eq_five (h : K4Hyp G) {u : G} (hu : orderOf u = 2) :
    ({y : G | orderOf y = 2 ∧ y ∈ cent G u} : Set G).ncard = 5 := by
  obtain ⟨W, hWle, hW⟩ := h.2.2.2.1 u hu
  have hcard : Nat.card ↥(cent G u) = 8 := h.2.1 u hu
  have hnab : ¬ IsMulCommutative ↥(cent G u) := h.2.2.1 u hu
  have hW'card : Nat.card ↥(W.subgroupOf (cent G u)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv]
    exact hW.1
  have hW'sq : ∀ w ∈ W.subgroupOf (cent G u), w * w = 1 := by
    intro w hw
    rw [Subgroup.mem_subgroupOf] at hw
    exact Subtype.ext (hW.2 (w : G) hw)
  have h5 := card_involutions_of_card_eight hcard hnab (W.subgroupOf (cent G u)) hW'card hW'sq
  rw [ncard_involutions_subgroup]
  exact h5

/-! ## An involution of `N_G(V)` outside `V` -/

/-- If `u ∈ N_G(V) ∖ V` is an involution then `C_G(u)` is not contained in `N_G(V)`: a subgroup
of order `8` of `N_G(V)` contains the normal four-group `V`. -/
theorem not_cent_le_normalizer_of_isV4 (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) {u : G}
    (huN : u ∈ Subgroup.normalizer (V : Set G)) (huV : u ∉ V) (hu2 : orderOf u = 2) :
    ¬ cent G u ≤ Subgroup.normalizer (V : Set G) := by
  intro hle
  have hQ8 : Nat.card ↥(cent G u) = 8 := h.2.1 u hu2
  set m : ℕ := Nat.card ↥(V ⊔ cent G u) with hm
  set n : ℕ := Nat.card ↥(V ⊓ cent G u) with hn
  have hmul : m * n = 32 := by
    have h' := card_sup_mul_card_inf_of_le_normalizer (A := V) (B := cent G u) hle
    rw [hV.1, hQ8] at h'
    rw [hm, hn]
    exact h'.trans (by norm_num)
  have hmdvd : m ∣ 24 := by
    have h' := Subgroup.card_dvd_of_le (sup_le Subgroup.le_normalizer hle)
    rw [card_normalizer_eq h hV, ← hm] at h'
    exact h'
  have hm8 : m = 8 := by
    have hle8 : 8 ≤ m := by
      have h' := Subgroup.card_dvd_of_le (le_sup_right : cent G u ≤ V ⊔ cent G u)
      rw [hQ8, ← hm] at h'
      exact Nat.le_of_dvd Nat.card_pos h'
    have hdvd8 : m ∣ 8 := Nat.dvd_gcd hmdvd ⟨n, hmul.symm⟩
    exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd8) hle8
  have hn4 : n = 4 := by
    rw [hm8] at hmul
    omega
  have hVle : V ≤ cent G u := by
    have heq : V ⊓ cent G u = V :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hV.1, ← hn, hn4])
    rw [← heq]
    exact inf_le_right
  have huCV : u ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.mem_centralizer_iff.mpr
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mp (hVle hv))
  rw [centralizer_eq_self_of_isV4 h hV] at huCV
  exact huV huCV

/-- For an involution `u ∈ N_G(V) ∖ V` there are exactly two involutions outside `N_G(V)` that
commute with `u`: `C_G(u) ≅ D₈` has five involutions, three of which lie in `N_G(V)`. -/
theorem card_involutions_cent_diff_normalizer (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) {u : G}
    (huN : u ∈ Subgroup.normalizer (V : Set G)) (huV : u ∉ V) (hu2 : orderOf u = 2) :
    ({y : G | orderOf y = 2 ∧ u * y = y * u ∧ y ∉ Subgroup.normalizer (V : Set G)} : Set G).ncard
      = 2 := by
  set H : Subgroup G := Subgroup.normalizer (V : Set G) with hH
  have hW : IsV4 (cent G u ⊓ H) := isV4_centralizer_inf_normalizer h hV huN huV hu2
  have hset : ({y : G | orderOf y = 2 ∧ u * y = y * u ∧ y ∉ H} : Set G) =
      ({y : G | orderOf y = 2 ∧ y ∈ cent G u} : Set G) \
        ({y : G | orderOf y = 2 ∧ y ∈ cent G u ⊓ H} : Set G) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨hy2, hyc, hyH⟩
      exact ⟨⟨hy2, Subgroup.mem_centralizer_singleton_iff.mpr hyc.symm⟩, fun h => hyH h.2.2⟩
    · rintro ⟨⟨hy2, hyc⟩, hyH⟩
      have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
      exact ⟨hy2, hyu.symm, fun hh => hyH ⟨hy2, hyc, hh⟩⟩
  have hsub : ({y : G | orderOf y = 2 ∧ y ∈ cent G u ⊓ H} : Set G) ⊆
      ({y : G | orderOf y = 2 ∧ y ∈ cent G u} : Set G) := by
    rintro y ⟨hy2, hy⟩
    exact ⟨hy2, hy.1⟩
  rw [hset, Set.ncard_sdiff hsub, card_involutions_cent_eq_five h hu2,
    IsV4.ncard_involutions hW]

/-! ## An involution outside `N_G(V)` -/

/-- For an involution `u ∉ N_G(V)`, the intersection `C_G(u) ⊓ N_G(V)` contains at most one
involution.  Its order divides `8`; order `8` is impossible because `C_G(u) ⊆ N_G(V)` would
force `u ∈ V ⊆ N_G(V)`, and order `4` is impossible because such a subgroup meets the normal
four-group `V` in a non-identity element, again forcing `u ∈ N_G(V)`. -/
theorem card_involutions_cent_inf_normalizer_le_one (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V)
    {u : G} (huH : u ∉ Subgroup.normalizer (V : Set G)) (hu2 : orderOf u = 2) :
    ({y : G | orderOf y = 2 ∧ y ∈ cent G u ⊓ Subgroup.normalizer (V : Set G)} : Set G).ncard
      ≤ 1 := by
  set H : Subgroup G := Subgroup.normalizer (V : Set G) with hH
  set n : ℕ := Nat.card ↥(cent G u ⊓ H) with hn
  have h8 : Nat.card ↥(cent G u) = 8 := h.2.1 u hu2
  have h24 : Nat.card ↥H = 24 := card_normalizer_eq h hV
  have hdvd : n ∣ 8 := by
    have h' := Subgroup.card_dvd_of_le (inf_le_left : cent G u ⊓ H ≤ cent G u)
    rw [h8, ← hn] at h'
    exact h'
  have hVleH : V ≤ H := Subgroup.le_normalizer
  have hne8 : n ≠ 8 := by
    intro h8'
    have heq : cent G u ⊓ H = cent G u :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, ← hn, h8'])
    have hmem : u ∈ cent G u ⊓ H := by
      rw [heq]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    exact huH hmem.2
  have hne4 : n ≠ 4 := by
    intro h4
    have h4' : Nat.card ↥(cent G u ⊓ H) = 4 := by rw [← hn]; exact h4
    set D : Subgroup G := cent G u ⊓ H with hD
    have hDV : D ≤ Subgroup.normalizer (V : Set G) := by
      rw [hD, hH]; exact inf_le_right
    have hD4 : Nat.card ↥D = 4 := by rw [hD]; exact h4'
    have hmul := card_sup_mul_card_inf_of_le_normalizer (A := V) (B := D) hDV
    rw [hV.1, hD4] at hmul
    have hsupdvd : Nat.card ↥(V ⊔ D) ∣ 24 := by
      have h' := Subgroup.card_dvd_of_le (sup_le Subgroup.le_normalizer hDV)
      rwa [card_normalizer_eq h hV] at h'
    have hinfdvd : Nat.card ↥(V ⊓ D) ∣ 4 := by
      have h' := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ D ≤ V)
      rwa [hV.1] at h'
    obtain ⟨j, hj, hji⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp hinfdvd
    interval_cases j
    · have h1 : Nat.card ↥(V ⊓ D) = 1 := by simpa using hji
      rw [h1, mul_one] at hmul
      have h16 : Nat.card ↥(V ⊔ D) = 16 := by rw [hmul]
      rw [h16] at hsupdvd
      norm_num at hsupdvd
    · have h2 : Nat.card ↥(V ⊓ D) = 2 := by simpa using hji
      obtain ⟨z, hz2⟩ : ∃ z : ↥(V ⊓ D), z ≠ 1 := by
        haveI : Nontrivial ↥(V ⊓ D) := by
          haveI := Fintype.ofFinite ↥(V ⊓ D)
          rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, h2]
          norm_num
        exact ⟨Classical.choose (exists_ne (1 : ↥(V ⊓ D))),
          Classical.choose_spec (exists_ne (1 : ↥(V ⊓ D)))⟩
      have hzG : (z : G) ≠ 1 := fun hh => hz2 (Subtype.ext hh)
      have hzV : (z : G) ∈ V := z.2.1
      have hzD : (z : G) ∈ D := z.2.2
      have hzu : u * (z : G) = (z : G) * u :=
        (Subgroup.mem_centralizer_singleton_iff.mp hzD.1).symm
      have hmem : u ∈ Subgroup.normalizer (V : Set G) :=
        cent_le_normalizer_of_isV4 h hV hzV hzG
          (Subgroup.mem_centralizer_singleton_iff.mpr hzu)
      exact huH (by rw [← hH] at hmem; exact hmem)
    · have h4'' : Nat.card ↥(V ⊓ D) = 4 := by simpa using hji
      have hVleD : V ≤ D := by
        have heq : V ⊓ D = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hV.1, h4''])
        rw [← heq]
        exact inf_le_right
      have hmem : u ∈ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact Subgroup.mem_centralizer_singleton_iff.mp (hVleD hv).1
      rw [centralizer_eq_self_of_isV4 h hV] at hmem
      exact huH (hVleH hmem)
  have hnle2 : n ≤ 2 := by
    obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 3)).mp hdvd
    interval_cases i
    · have h1 : n = 1 := by simpa using hni
      omega
    · have h2 : n = 2 := by simpa using hni
      omega
    · exact absurd (show n = 4 by simpa using hni) hne4
    · exact absurd (show n = 8 by simpa using hni) hne8
  have hsub : ({y : G | orderOf y = 2 ∧ y ∈ cent G u ⊓ H} : Set G) ⊆
      ((cent G u ⊓ H : Subgroup G) : Set G) \ {1} := by
    rintro y ⟨hy2, hy⟩
    refine ⟨hy, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h1
    rw [h1] at hy2
    simp at hy2
  calc ({y : G | orderOf y = 2 ∧ y ∈ cent G u ⊓ H} : Set G).ncard
      ≤ (((cent G u ⊓ H : Subgroup G) : Set G) \ {1}).ncard := Set.ncard_le_ncard hsub
    _ = n - 1 := by
          rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem (cent G u ⊓ H)),
            show (((cent G u ⊓ H : Subgroup G) : Set G)).ncard = n from
              (Nat.card_coe_set_eq _).symm.trans hn.symm]
    _ ≤ 1 := by omega

/-! ## The lower bound: twelve involutions lie outside `N_G(V)` -/

/-- Variant of `card_involutions_cent_diff_normalizer` with the commuting condition written last. -/
theorem card_involutions_cent_diff_normalizer' (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) {u : G}
    (huN : u ∈ Subgroup.normalizer (V : Set G)) (huV : u ∉ V) (hu2 : orderOf u = 2) :
    ({y : G | orderOf y = 2 ∧ y ∉ Subgroup.normalizer (V : Set G) ∧ u * y = y * u} : Set G).ncard
      = 2 := by
  have h1 : ({y : G | orderOf y = 2 ∧ y ∉ Subgroup.normalizer (V : Set G) ∧ u * y = y * u} :
      Set G) = {y : G | orderOf y = 2 ∧ (u * y = y * u ∧ y ∉ Subgroup.normalizer (V : Set G))} := by
    ext y
    simp only [Set.mem_setOf_eq]
    tauto
  rw [h1]
  exact card_involutions_cent_diff_normalizer h hV huN huV hu2

/-- `N_G(V)` contains exactly six involutions outside `V`. -/
theorem ncard_involutions_normalizer_diff (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) :
    Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (V : Set G) ∧ u ∉ V} = 6 := by
  have h9 : ({u : G | orderOf u = 2 ∧ u ∈ Subgroup.normalizer (V : Set G)} : Set G).ncard = 9 :=
    card_involutions_normalizer h hV
  have h3 : ({u : G | orderOf u = 2 ∧ u ∈ V} : Set G).ncard = 3 := IsV4.ncard_involutions hV
  have hset : ({u : G | orderOf u = 2 ∧ u ∈ Subgroup.normalizer (V : Set G) ∧ u ∉ V} : Set G) =
      ({u : G | orderOf u = 2 ∧ u ∈ Subgroup.normalizer (V : Set G)} : Set G) \
        ({u : G | orderOf u = 2 ∧ u ∈ V} : Set G) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun hh => h3 hh.2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun hh => h3 ⟨h1, hh⟩⟩
  have hsub : ({u : G | orderOf u = 2 ∧ u ∈ V} : Set G) ⊆
      ({u : G | orderOf u = 2 ∧ u ∈ Subgroup.normalizer (V : Set G)} : Set G) := by
    rintro u ⟨hu2, huV⟩
    exact ⟨hu2, Subgroup.le_normalizer huV⟩
  have hbridge : Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (V : Set G) ∧ u ∉ V}
      = ({u : G | orderOf u = 2 ∧ u ∈ Subgroup.normalizer (V : Set G) ∧ u ∉ V} : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [hbridge, hset, Set.ncard_sdiff hsub, h9, h3]

/-- At least twelve involutions of `G` lie outside `N_G(V)`: each of the six involutions of
`N_G(V) ∖ V` commutes with exactly two involutions outside `N_G(V)`, and no involution outside
`N_G(V)` commutes with two of them. -/
theorem twelve_le_ncard_involutions_not_mem_normalizer (h : K4Hyp G) {V : Subgroup G}
    (hV : IsV4 V) :
    12 ≤ ({y : G | orderOf y = 2 ∧ y ∉ Subgroup.normalizer (V : Set G)} : Set G).ncard := by
  set H : Subgroup G := Subgroup.normalizer (V : Set G) with hH
  have hA6 : Nat.card {u : G // orderOf u = 2 ∧ u ∈ H ∧ u ∉ V} = 6 :=
    ncard_involutions_normalizer_diff h hV
  let B : Type := {y : G // orderOf y = 2 ∧ y ∉ H}
  let R : Type := (u : {u : G // orderOf u = 2 ∧ u ∈ H ∧ u ∉ V}) ×
    {y : G // orderOf y = 2 ∧ y ∉ H ∧ (u.1 : G) * y = y * (u.1 : G)}
  have hpart : ∀ a : {u : G // orderOf u = 2 ∧ u ∈ H ∧ u ∉ V},
      Nat.card {y : G // orderOf y = 2 ∧ y ∉ H ∧ (a.1 : G) * y = y * (a.1 : G)} = 2 := by
    intro a
    have hbridge : Nat.card {y : G // orderOf y = 2 ∧ y ∉ H ∧ (a.1 : G) * y = y * (a.1 : G)}
        = ({y : G | orderOf y = 2 ∧ y ∉ H ∧ (a.1 : G) * y = y * (a.1 : G)} : Set G).ncard :=
      Nat.card_coe_set_eq _
    rw [hbridge]
    exact card_involutions_cent_diff_normalizer' h hV a.2.2.1 a.2.2.2 a.2.1
  have hR12 : Nat.card R = 12 := by
    letI := Fintype.ofFinite {u : G // orderOf u = 2 ∧ u ∈ H ∧ u ∉ V}
    rw [Nat.card_sigma]
    rw [Finset.sum_congr rfl (fun a _ => hpart a)]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul, hA6]
  have hinj : Function.Injective (fun p : R => (⟨p.2.1, p.2.2.1, p.2.2.2.1⟩ : B)) := by
    rintro ⟨a, y⟩ ⟨a', y'⟩ heq
    have heqG : (y : G) = (y' : G) := congrArg Subtype.val heq
    have key : ∀ (b : {u : G // orderOf u = 2 ∧ u ∈ H ∧ u ∉ V})
        (w : {y : G // orderOf y = 2 ∧ y ∉ H ∧ (b.1 : G) * y = y * (b.1 : G)}),
        (y : G) = (w : G) →
        (b.1 : G) ∈ ({z : G | orderOf z = 2 ∧ z ∈ cent G (y : G) ⊓ H} : Set G) := by
      intro b w hw
      exact ⟨b.2.1,
        Subgroup.mem_centralizer_singleton_iff.mpr (by rw [hw]; exact w.2.2.2), b.2.2.1⟩
    have hsub : ({z : G | orderOf z = 2 ∧ z ∈ cent G (y : G) ⊓ H} : Set G).ncard ≤ 1 :=
      card_involutions_cent_inf_normalizer_le_one h hV y.2.2.1 y.2.1
    have h1 : (a.1 : G) = (a'.1 : G) :=
      (Set.ncard_le_one_iff).mp hsub (key a y rfl) (key a' y' heqG)
    have ha : a = a' := Subtype.ext h1
    subst ha
    exact congrArg (fun w => (⟨a, w⟩ : R)) (Subtype.ext heqG)
  have hRle : Nat.card R ≤ Nat.card B :=
    Nat.card_le_card_of_injective (fun p : R => (⟨p.2.1, p.2.2.1, p.2.2.2.1⟩ : B)) hinj
  have h12 : 12 ≤ Nat.card B := by omega
  have hB : Nat.card B = ({y : G | orderOf y = 2 ∧ y ∉ H} : Set G).ncard :=
    (Nat.card_coe_set_eq _).symm
  rw [hB] at h12
  exact h12

end Work.BSW.Cases.K4
