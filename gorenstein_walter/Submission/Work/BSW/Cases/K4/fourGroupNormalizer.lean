/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# The normalizer of a four-group in the Bender `|K| = 4` setting

Under `Work.BSW.Cases.K4.K4Hyp G` (all involutions are conjugate, every involution centralizer has
order `8` and is non-abelian, and it contains a Klein four-group) we prove, for every Klein
four-group `V ≤ G`:

* `C_G(V) = V`,
* `|N_G(V)| = 24`,
* the normalizer `N_G(V)` contains exactly `9` involutions.
-/
import Mathlib
import Submission.Work.BSW.Cases.K4.K4Hyp
import Submission.Work.COPR.card_mul_of_fibers

namespace Work.BSW.Cases.K4

open Subgroup Work.GW2

section Setup

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary structure of a Klein four group -/

/-- A Klein four group is commutative. -/
theorem IsV4.comm {V : Subgroup G} (hV : IsV4 V) {a b : G} (ha : a ∈ V) (hb : b ∈ V) :
    a * b = b * a := by
  have ha2 : a * a = 1 := hV.2 a ha
  have hb2 : b * b = 1 := hV.2 b hb
  have hab2 : (a * b) * (a * b) = 1 := hV.2 (a * b) (V.mul_mem ha hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab2).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha2]

/-- A non-identity element of a Klein four group has order two. -/
theorem IsV4.orderOf_eq_two {V : Subgroup G} (hV : IsV4 V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    orderOf v = 2 := by
  refine orderOf_eq_prime (p := 2) ?_ hv1
  rw [pow_two]
  exact hV.2 v hv

/-- `V` is contained in the centralizer of each of its elements. -/
theorem IsV4.le_cent {V : Subgroup G} (hV : IsV4 V) {v : G} (hv : v ∈ V) : V ≤ cent G v := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact IsV4.comm hV hy hv

/-- A Klein four group has a non-identity element. -/
theorem IsV4.exists_ne_one {V : Subgroup G} (hV : IsV4 V) : ∃ u ∈ V, u ≠ 1 := by
  by_contra h
  push_neg at h
  have hbot : V = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [h x hx]
  rw [hbot] at hV
  have h1 : Nat.card ↥(⊥ : Subgroup G) = 4 := hV.1
  rw [Subgroup.card_bot] at h1
  exact absurd h1 (by norm_num)

/-- A Klein four group has exactly three non-identity elements. -/
theorem card_subtype_ne_one_of_isV4 {V : Subgroup G} (hV : IsV4 V) :
    Nat.card {x : ↥V // x ≠ 1} = 3 := by
  haveI : Fintype ↥V := Fintype.ofFinite _
  haveI : Fintype {x : ↥V // x ≠ 1} := Fintype.ofFinite _
  haveI : Fintype {x : ↥V // x = 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : ↥V => x = 1)]
  have h1 : Fintype.card ↥V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hV.1
  have h2 : Fintype.card {x : ↥V // x = 1} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨1, rfl⟩, fun y => Subtype.ext y.2⟩
  omega

/-- A Klein four group has exactly three non-identity elements (as elements of the ambient
group). -/
theorem card_ne_one_of_isV4 {V : Subgroup G} (hV : IsV4 V) :
    Nat.card {x : G // x ∈ V ∧ x ≠ 1} = 3 := by
  rw [← card_subtype_ne_one_of_isV4 hV]
  exact Nat.card_congr {
    toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun hc => x.2.2 (Subtype.ext_iff.mp hc)⟩
    invFun := fun x => ⟨x.1.1, x.1.2, fun hc => x.2 (Subtype.ext hc)⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl }

/-- Every divisor of `8` is `1`, `2`, `4` or `8`. -/
theorem dvd_eight_cases {n : ℕ} (h : n ∣ 8) : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  obtain ⟨k, hk⟩ := h
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hk8 : k ≤ 8 := by nlinarith [hk, Nat.zero_le k]
  interval_cases k <;> omega

/-! ## A subgroup of the centre of index two -/

/-- A finite group `H` whose subgroup `A ≤ Z(H)` has index `2` (expressed as `|H| = 2 * |A|`) is
commutative. -/
theorem isMulCommutative_of_le_center_of_two_mul_card {H : Type*} [Group H] [Finite H]
    (A : Subgroup H) (hA : A ≤ Subgroup.center H) (hcard : 2 * Nat.card ↥A = Nat.card H) :
    IsMulCommutative H := by
  have hnormal : A.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff]
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A : Set H))
    rw [Subgroup.le_centralizer_iff, Subgroup.coe_top, Subgroup.centralizer_univ]
    exact hA
  have hquot : Nat.card (H ⧸ A) ∣ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup A
    rw [← hcard] at h
    refine ⟨1, ?_⟩
    rw [mul_one]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  haveI : IsCyclic (H ⧸ A) := isCyclic_of_card_dvd_prime (p := 2) hquot
  exact (QuotientGroup.mk' A).isMulCommutative_of_isCyclic_of_ker_le_center (by
    rw [QuotientGroup.ker_mk']
    exact hA)

/-- A non-abelian group of order `8` has a centre of order `2`. -/
theorem card_center_eq_two_of_card_eq_eight {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = 8) (hnab : ¬ IsMulCommutative H) :
    Nat.card ↥(Subgroup.center H) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 H := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  haveI : Nontrivial H := hpg.nontrivial_iff_card.mpr ⟨3, by norm_num, by rw [hcard]; norm_num⟩
  have hnt : Nontrivial ↥(Subgroup.center H) := hpg.center_nontrivial
  have hdvd : Nat.card ↥(Subgroup.center H) ∣ 8 := by
    have h := Subgroup.card_dvd_of_le (le_top : Subgroup.center H ≤ ⊤)
    rw [Subgroup.card_top, hcard] at h
    exact h
  have hne8 : Nat.card ↥(Subgroup.center H) ≠ 8 := by
    intro h8
    refine hnab ⟨⟨fun a b => ?_⟩⟩
    have htop : Subgroup.center H = ⊤ :=
      Subgroup.eq_top_of_card_eq (G := H) (H := Subgroup.center H) (by rw [h8, hcard])
    have hb : b ∈ Subgroup.center H := by rw [htop]; exact Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hb a
  have hne4 : Nat.card ↥(Subgroup.center H) ≠ 4 := by
    intro h4
    exact hnab (isMulCommutative_of_le_center_of_two_mul_card (Subgroup.center H) le_rfl
      (by rw [h4, hcard]))
  haveI : Fintype ↥(Subgroup.center H) := Fintype.ofFinite _
  have h2 : 2 ≤ Nat.card ↥(Subgroup.center H) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff_nontrivial.mpr hnt
  rcases dvd_eight_cases hdvd with h1 | h2' | h4 | h8
  · omega
  · omega
  · exact absurd h4 hne4
  · exact absurd h8 hne8

/-- The centre of a nontrivial finite `p`-group contains an element of order `p`. -/
theorem exists_center_involution {H : Type*} [Group H] [Finite H] (p : ℕ) [Fact p.Prime]
    (hpg : IsPGroup p H) (hnt : Nontrivial H) :
    ∃ z : H, z ∈ Subgroup.center H ∧ orderOf z = p := by
  haveI : Nontrivial ↥(Subgroup.center H) := hpg.center_nontrivial
  have hZ : IsPGroup p ↥(Subgroup.center H) := hpg.to_subgroup _
  obtain ⟨m, hmpos, hm⟩ := (hZ.nontrivial_iff_card).mp inferInstance
  have hdvd : p ∣ Nat.card ↥(Subgroup.center H) := by
    rw [hm]
    refine ⟨p ^ (m - 1), ?_⟩
    calc p ^ m = p ^ (m - 1) * p ^ 1 :=
          (Nat.pow_sub_mul_pow (a := p) (m := 1) (n := m) (by omega)).symm
      _ = p ^ (m - 1) * p := by rw [pow_one]
      _ = p * p ^ (m - 1) := by rw [mul_comm]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center H)) p hdvd
  exact ⟨z, z.2, by rwa [Subgroup.orderOf_coe z]⟩

/-! ## Sylow `2`-subgroups -/

/-- Every Sylow `2`-subgroup of `G` has order `8` in the `K4` setting. -/
theorem card_sylow_two_eq_eight (h : K4Hyp G) (P : Sylow 2 G) :
    Nat.card ↥(P : Subgroup G) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := h.1
  have hC8 : Nat.card ↥(cent G t) = 8 := h.2.1 t ht
  have hC2 : IsPGroup 2 ↥(cent G t) := IsPGroup.of_card (n := 3) (by rw [hC8]; norm_num)
  obtain ⟨Q, hCQ⟩ := hC2.exists_le_sylow
  have hQ8 : 8 ≤ Nat.card ↥(Q : Subgroup G) := by
    have h1 : Nat.card ↥(cent G t) ≤ Nat.card ↥(Q : Subgroup G) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hCQ) (Subgroup.inclusion_injective hCQ)
    omega
  have hPQ : Nat.card ↥(P : Subgroup G) = Nat.card ↥(Q : Subgroup G) :=
    Nat.card_congr (Sylow.equiv P Q).toEquiv
  have h8P : 8 ≤ Nat.card ↥(P : Subgroup G) := by rw [hPQ]; exact hQ8
  have hnt : Nontrivial ↥(P : Subgroup G) := by
    haveI : Fintype ↥(P : Subgroup G) := Fintype.ofFinite _
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨z, hzZ, hzord⟩ := exists_center_involution 2 P.isPGroup' hnt
  have hzord' : orderOf ((z : ↥(P : Subgroup G)) : G) = 2 := by
    rw [Subgroup.orderOf_coe z]; exact hzord
  have hle : Nat.card ↥(P : Subgroup G) ≤ Nat.card ↥(cent G ((z : ↥(P : Subgroup G)) : G)) := by
    have hsub : (P : Subgroup G) ≤ cent G ((z : ↥(P : Subgroup G)) : G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : (⟨x, hx⟩ : ↥(P : Subgroup G)) * z = z * ⟨x, hx⟩ :=
        Subgroup.mem_center_iff.mp hzZ ⟨x, hx⟩
      exact congrArg (fun w : ↥(P : Subgroup G) => (w : G)) h2
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hsub)
  rw [h.2.1 ((z : ↥(P : Subgroup G)) : G) hzord'] at hle
  omega

/-! ## Involution centralizers -/

/-- Distinct involutions have distinct centralizers in the `K4` setting. -/
theorem cent_ne_cent_of_ne (h : K4Hyp G) {u w : G} (hu : orderOf u = 2) (hw : orderOf w = 2)
    (huw : u ≠ w) : cent G u ≠ cent G w := by
  intro heq
  have huP : u ∈ cent G u := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hwP : w ∈ cent G u := by
    rw [heq]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hZu : (⟨u, huP⟩ : ↥(cent G u)) ∈ Subgroup.center ↥(cent G u) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hZw : (⟨w, hwP⟩ : ↥(cent G u)) ∈ Subgroup.center ↥(cent G u) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : (g : G) ∈ cent G w := by rw [← heq]; exact g.2
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hZcard : Nat.card ↥(Subgroup.center ↥(cent G u)) = 2 :=
    card_center_eq_two_of_card_eq_eight (h.2.1 u hu) (h.2.2.1 u hu)
  have huZord : orderOf (⟨u, huP⟩ : ↥(cent G u)) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨u, huP⟩ : ↥(cent G u))]; exact hu
  have hgen : Subgroup.zpowers (⟨u, huP⟩ : ↥(cent G u)) = Subgroup.center ↥(cent G u) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hZu) ?_
    rw [Nat.card_zpowers, hZcard, huZord]
  have hmem : (⟨w, hwP⟩ : ↥(cent G u)) ∈ Subgroup.zpowers (⟨u, huP⟩ : ↥(cent G u)) := by
    rw [hgen]; exact hZw
  rcases mem_zpowers_eq_one_or huZord hmem with h1 | h1
  · have : w = 1 := Subtype.ext_iff.mp h1
    rw [this, orderOf_one] at hw
    exact absurd hw (by norm_num)
  · exact huw (Subtype.ext_iff.mp h1).symm

/-- `C_G(V) = V` for a Klein four group `V` in the `K4` setting. -/
theorem centralizer_eq_self_of_isV4 (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) :
    Subgroup.centralizer (V : Set G) = V := by
  haveI : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (IsV4.comm hV a.2 b.2)⟩⟩
  obtain ⟨u, huV, hu1⟩ := hV.exists_ne_one
  have hu2 : orderOf u = 2 := hV.orderOf_eq_two huV hu1
  have hcle : Subgroup.centralizer (V : Set G) ≤ cent G u := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx u huV).symm
  have hge : 4 ≤ Nat.card ↥(Subgroup.centralizer (V : Set G)) := by
    have hdvd : Nat.card ↥V ∣ Nat.card ↥(Subgroup.centralizer (V : Set G)) :=
      Subgroup.card_dvd_of_le (Subgroup.le_centralizer V)
    rw [hV.1] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hle : Nat.card ↥(Subgroup.centralizer (V : Set G)) ≤ 8 := by
    have hdvd : Nat.card ↥(Subgroup.centralizer (V : Set G)) ∣ Nat.card ↥(cent G u) :=
      Subgroup.card_dvd_of_le hcle
    rw [h.2.1 u hu2] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hdvdC : Nat.card ↥(Subgroup.centralizer (V : Set G)) ∣ 8 := by
    have hdvd : Nat.card ↥(Subgroup.centralizer (V : Set G)) ∣ Nat.card ↥(cent G u) :=
      Subgroup.card_dvd_of_le hcle
    rwa [h.2.1 u hu2] at hdvd
  have hsplit : Nat.card ↥(Subgroup.centralizer (V : Set G)) = 4 ∨
      Nat.card ↥(Subgroup.centralizer (V : Set G)) = 8 := by
    rcases dvd_eight_cases hdvdC with h1 | h2' | h4 | h8
    · omega
    · omega
    · exact Or.inl h4
    · exact Or.inr h8
  rcases hsplit with h4 | h8
  · exact (Subgroup.eq_of_le_of_card_ge (Subgroup.le_centralizer V) (by rw [h4, hV.1])).symm
  · have heqC : Subgroup.centralizer (V : Set G) = cent G u :=
      Subgroup.eq_of_le_of_card_ge hcle (by rw [h8, h.2.1 u hu2])
    have hVcenter : V.subgroupOf (cent G u) ≤ Subgroup.center ↥(cent G u) := by
      intro v hv
      rw [Subgroup.mem_subgroupOf] at hv
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : (g : G) ∈ Subgroup.centralizer (V : Set G) := by rw [heqC]; exact g.2
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg (v : G) hv).symm
    have hcardA : 2 * Nat.card ↥(V.subgroupOf (cent G u)) = Nat.card ↥(cent G u) := by
      have h1 : Nat.card ↥(V.subgroupOf (cent G u)) = Nat.card ↥V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hV.le_cent huV)).toEquiv
      rw [h1, hV.1, h.2.1 u hu2]
    exact absurd (isMulCommutative_of_le_center_of_two_mul_card _ hVcenter hcardA)
      (h.2.2.1 u hu2)

/-- `C_G(u)` is contained in `N_G(V)` for `u` a non-identity element of the Klein four group `V`. -/
theorem cent_le_normalizer_of_isV4 (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) {u : G}
    (huV : u ∈ V) (hu1 : u ≠ 1) : cent G u ≤ Subgroup.normalizer (V : Set G) :=
  le_normalizer_of_two_mul_card (hV.le_cent huV)
    (by rw [h.2.1 u (hV.orderOf_eq_two huV hu1), hV.1])

/-- Distinct non-identity elements of a Klein four group have centralizers meeting exactly in
`V`. -/
theorem inf_cent_eq_of_isV4 (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) {u w : G}
    (huV : u ∈ V) (hu1 : u ≠ 1) (hwV : w ∈ V) (hw1 : w ≠ 1) (huw : u ≠ w) :
    cent G u ⊓ cent G w = V := by
  have hu2 : orderOf u = 2 := hV.orderOf_eq_two huV hu1
  have hw2 : orderOf w = 2 := hV.orderOf_eq_two hwV hw1
  have hle : V ≤ cent G u ⊓ cent G w := fun x hx => ⟨hV.le_cent huV hx, hV.le_cent hwV hx⟩
  have hge : 4 ≤ Nat.card ↥(cent G u ⊓ cent G w) := by
    have hdvd' : Nat.card ↥V ∣ Nat.card ↥(cent G u ⊓ cent G w) :=
      Subgroup.card_dvd_of_le hle
    rw [hV.1] at hdvd'
    exact Nat.le_of_dvd Nat.card_pos hdvd'
  have hne : Nat.card ↥(cent G u ⊓ cent G w) ≠ 8 := by
    intro h8
    have heq : cent G u ⊓ cent G w = cent G u :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h.2.1 u hu2])
    have hle' : cent G u ≤ cent G w := by rw [← heq]; exact inf_le_right
    exact cent_ne_cent_of_ne h hu2 hw2 huw
      (Subgroup.eq_of_le_of_card_ge hle' (by rw [h.2.1 u hu2, h.2.1 w hw2]))
  have hdvd : Nat.card ↥(cent G u ⊓ cent G w) ∣ 8 := by
    have h2 := Subgroup.card_dvd_of_le (inf_le_left : cent G u ⊓ cent G w ≤ cent G u)
    rwa [h.2.1 u hu2] at h2
  have hcard : Nat.card ↥(cent G u ⊓ cent G w) = 4 := by
    rcases dvd_eight_cases hdvd with h1 | h2' | h4 | h8
    · omega
    · omega
    · exact h4
    · exact absurd h8 hne
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hV.1])).symm


/-- Conjugation of a fixed non-identity element `u` of `V` by an element of `N_G(V)`. -/
def conjV (V : Subgroup G) (u : G) (huV : u ∈ V) (hu1 : u ≠ 1) :
    ↥(Subgroup.normalizer (V : Set G)) → {x : G // x ∈ V ∧ x ≠ 1} := fun n =>
  ⟨(n : G) * u * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 u).mp huV, by
    intro hc
    exact hu1 (by
      have h2 : (n : G) * u * (n : G)⁻¹ = (1 : G) := hc
      have h3 := congrArg (fun z : G => (n : G)⁻¹ * z * (n : G)) h2
      simpa [mul_assoc] using h3)⟩

/-- The value of `conjV`. -/
@[simp] theorem conjV_coe (V : Subgroup G) (u : G) (huV : u ∈ V) (hu1 : u ≠ 1)
    (n : ↥(Subgroup.normalizer (V : Set G))) :
    (conjV V u huV hu1 n).1 = (n : G) * u * (n : G)⁻¹ := rfl

/-- Each non-identity element lies in its own orbit under conjugation. -/
theorem conjV_mem_range_self {V : Subgroup G} {u : G} (huV : u ∈ V) (hu1 : u ≠ 1) :
    (⟨u, huV, hu1⟩ : {x : G // x ∈ V ∧ x ≠ 1}) ∈ Set.range (conjV V u huV hu1) :=
  ⟨1, by apply Subtype.ext; simp⟩

/-- The conjugation relation on the non-identity elements of `V` is symmetric. -/
theorem conjV_symm {V : Subgroup G} {x y : {x : G // x ∈ V ∧ x ≠ 1}}
    (h : y ∈ Set.range (conjV V x.1 x.2.1 x.2.2)) :
    x ∈ Set.range (conjV V y.1 y.2.1 y.2.2) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n⁻¹, ?_⟩
  have h1 : (n : G) * x.1 * (n : G)⁻¹ = y.1 := by
    have h2 := congrArg (fun w : {x : G // x ∈ V ∧ x ≠ 1} => w.1) hn
    simpa only [conjV_coe] using h2
  apply Subtype.ext
  show ((n⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * y.1
    * ((n⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ = x.1
  rw [show ((n⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) = (n : G)⁻¹ from rfl, ← h1]
  group

/-- The conjugation relation on the non-identity elements of `V` is transitive. -/
theorem conjV_trans {V : Subgroup G} {x y z : {x : G // x ∈ V ∧ x ≠ 1}}
    (h1 : y ∈ Set.range (conjV V x.1 x.2.1 x.2.2))
    (h2 : z ∈ Set.range (conjV V y.1 y.2.1 y.2.2)) :
    z ∈ Set.range (conjV V x.1 x.2.1 x.2.2) := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  refine ⟨m * n, ?_⟩
  have hn' : (n : G) * x.1 * (n : G)⁻¹ = y.1 := by
    have h := congrArg (fun w : {x : G // x ∈ V ∧ x ≠ 1} => w.1) hn
    simpa only [conjV_coe] using h
  have hm' : (m : G) * y.1 * (m : G)⁻¹ = z.1 := by
    have h := congrArg (fun w : {x : G // x ∈ V ∧ x ≠ 1} => w.1) hm
    simpa only [conjV_coe] using h
  apply Subtype.ext
  show ((m * n : ↥(Subgroup.normalizer (V : Set G))) : G) * x.1
    * ((m * n : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ = z.1
  rw [show ((m * n : ↥(Subgroup.normalizer (V : Set G))) : G) = (m : G) * (n : G) from rfl,
    show (m : G) * (n : G) * x.1 * ((m : G) * (n : G))⁻¹
      = (m : G) * ((n : G) * x.1 * (n : G)⁻¹) * (m : G)⁻¹ from by group, hn', hm']

/-- The relation "is a conjugate of" on `V #` is symmetric, as a set statement. -/
theorem conjV_range_symm {V : Subgroup G} {x y : {x : G // x ∈ V ∧ x ≠ 1}}
    (h : y ∈ Set.range (conjV V x.1 x.2.1 x.2.2)) :
    x ∈ Set.range (conjV V y.1 y.2.1 y.2.2) := conjV_symm h

/-- The fibres of `conjV` over its image have cardinality `8`: the stabiliser of `u` is `C_G(u)`. -/
theorem conjV_fiber_card (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) {u : G} (huV : u ∈ V)
    (hu1 : u ≠ 1) (n₀ : ↥(Subgroup.normalizer (V : Set G))) :
    Nat.card {n : ↥(Subgroup.normalizer (V : Set G)) //
      conjV V u huV hu1 n = conjV V u huV hu1 n₀} = 8 := by
  have hmemN : cent G u ≤ Subgroup.normalizer (V : Set G) :=
    cent_le_normalizer_of_isV4 h hV huV hu1
  have hbij : Nat.card {n : ↥(Subgroup.normalizer (V : Set G)) //
        conjV V u huV hu1 n = conjV V u huV hu1 n₀} = Nat.card ↥(cent G u) :=
    Nat.card_congr {
      toFun := fun n => ⟨(n₀ : G)⁻¹ * (n.1 : G), by
        have hp : (n.1 : G) * u * (n.1 : G)⁻¹ = (n₀ : G) * u * (n₀ : G)⁻¹ := by
          have h1 := congrArg (fun w : {x : G // x ∈ V ∧ x ≠ 1} => w.1) n.2
          simpa only [conjV_coe] using h1
        have hconj : ((n₀ : G)⁻¹ * (n.1 : G)) * u * ((n₀ : G)⁻¹ * (n.1 : G))⁻¹ = u := by
          have h2 : (n₀ : G)⁻¹ * ((n.1 : G) * u * (n.1 : G)⁻¹) * (n₀ : G) = u := by
            rw [hp]; group
          calc ((n₀ : G)⁻¹ * (n.1 : G)) * u * ((n₀ : G)⁻¹ * (n.1 : G))⁻¹
              = (n₀ : G)⁻¹ * ((n.1 : G) * u * (n.1 : G)⁻¹) * (n₀ : G) := by group
            _ = u := h2
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc ((n₀ : G)⁻¹ * (n.1 : G)) * u
            = (((n₀ : G)⁻¹ * (n.1 : G)) * u * ((n₀ : G)⁻¹ * (n.1 : G))⁻¹)
                * ((n₀ : G)⁻¹ * (n.1 : G)) := by group
          _ = u * ((n₀ : G)⁻¹ * (n.1 : G)) := by rw [hconj]⟩
      invFun := fun y => ⟨⟨(n₀ : G) * (y : G),
          (Subgroup.normalizer (V : Set G)).mul_mem n₀.2 (hmemN y.2)⟩, by
        have hy : (y : G) * u * (y : G)⁻¹ = u := by
          calc (y : G) * u * (y : G)⁻¹ = u * (y : G) * (y : G)⁻¹ := by
                rw [Subgroup.mem_centralizer_singleton_iff.mp y.2]
            _ = u := by group
        apply Subtype.ext
        show (n₀ : G) * (y : G) * u * ((n₀ : G) * (y : G))⁻¹ = (n₀ : G) * u * (n₀ : G)⁻¹
        rw [show (n₀ : G) * (y : G) * u * ((n₀ : G) * (y : G))⁻¹
              = (n₀ : G) * ((y : G) * u * (y : G)⁻¹) * (n₀ : G)⁻¹ from by group, hy]⟩
      left_inv := fun n => by
        apply Subtype.ext
        apply Subtype.ext
        show (n₀ : G) * ((n₀ : G)⁻¹ * (n.1 : G)) = (n.1 : G)
        group
      right_inv := fun y => by
        apply Subtype.ext
        show (n₀ : G)⁻¹ * ((n₀ : G) * (y : G)) = (y : G)
        group }
  rw [hbij, h.2.1 u (hV.orderOf_eq_two huV hu1)]

/-- The corestriction of `conjV` to its range. -/
def conjVRange (V : Subgroup G) (u : G) (huV : u ∈ V) (hu1 : u ≠ 1) :
    ↥(Subgroup.normalizer (V : Set G)) → Set.range (conjV V u huV hu1) :=
  fun n => ⟨conjV V u huV hu1 n, Set.mem_range_self n⟩

/-- The fibres of the corestricted conjugation map all have cardinality `8`. -/
theorem conjVRange_fiber_card (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) {u : G}
    (huV : u ∈ V) (hu1 : u ≠ 1) (y : Set.range (conjV V u huV hu1)) :
    Nat.card {n : ↥(Subgroup.normalizer (V : Set G)) // conjVRange V u huV hu1 n = y} = 8 := by
  obtain ⟨n₀, hn₀⟩ := y.2
  have hconv : Nat.card {n : ↥(Subgroup.normalizer (V : Set G)) //
        conjVRange V u huV hu1 n = y} =
      Nat.card {n : ↥(Subgroup.normalizer (V : Set G)) //
        conjV V u huV hu1 n = conjV V u huV hu1 n₀} := Nat.card_congr {
    toFun := fun n => ⟨n.1, by
      have h2 := congrArg
        (fun w : Set.range (conjV V u huV hu1) => (w.1 : {x : G // x ∈ V ∧ x ≠ 1})) n.2
      exact h2.trans hn₀.symm⟩
    invFun := fun n => ⟨n.1, by
      refine Subtype.ext ?_
      show conjV V u huV hu1 n.1 = y.1
      rw [n.2, hn₀]⟩
    left_inv := fun n => rfl
    right_inv := fun n => rfl }
  rw [hconv]
  exact conjV_fiber_card h hV huV hu1 n₀

/-- Every orbit of the conjugation action of `N_G(V)` on `V #` has size `|N_G(V)| / 8`. -/
theorem card_normalizer_eq_eight_mul (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) {u : G}
    (huV : u ∈ V) (hu1 : u ≠ 1) :
    Nat.card ↥(Subgroup.normalizer (V : Set G)) =
      8 * Nat.card (Set.range (conjV V u huV hu1)) := by
  have h1 := Work.COPR.card_mul_of_fibers (conjVRange V u huV hu1) 8
    (fun y => conjVRange_fiber_card h hV huV hu1 y)
  rw [h1, mul_comm]

/-- Given a second non-identity element of `V`. -/
theorem exists_ne_of_card_three {V : Subgroup G} (hV : IsV4 V) (x : {x : G // x ∈ V ∧ x ≠ 1}) :
    ∃ y : {x : G // x ∈ V ∧ x ≠ 1}, y ≠ x := by
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set {x : G // x ∈ V ∧ x ≠ 1}) ⊆ {x} := fun z _ => by
    rw [Set.mem_singleton_iff]; exact hcon z
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_univ, Set.ncard_singleton] at hle
  have h3 := card_ne_one_of_isV4 hV
  omega

/-- The normalizer of a Klein four group has order `24` in the `K4` setting. -/
theorem card_normalizer_eq (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) :
    Nat.card ↥(Subgroup.normalizer (V : Set G)) = 24 := by
  classical
  obtain ⟨u, huV, hu1⟩ := hV.exists_ne_one
  obtain ⟨y, hyx⟩ := exists_ne_of_card_three hV ⟨u, huV, hu1⟩
  obtain ⟨w, hwV, hw1, hwu⟩ : ∃ w ∈ V, w ≠ 1 ∧ w ≠ u :=
    ⟨y.1, y.2.1, y.2.2, fun hc => hyx (Subtype.ext hc)⟩
  have hu2 : orderOf u = 2 := hV.orderOf_eq_two huV hu1
  have hw2 : orderOf w = 2 := hV.orderOf_eq_two hwV hw1
  set s : ℕ := Nat.card (Set.range (conjV V u huV hu1)) with hs
  have hNcard : Nat.card ↥(Subgroup.normalizer (V : Set G)) = 8 * s :=
    card_normalizer_eq_eight_mul h hV huV hu1
  -- all orbits have the same size `s`
  have hsize : ∀ x : {x : G // x ∈ V ∧ x ≠ 1},
      Nat.card (Set.range (conjV V x.1 x.2.1 x.2.2)) = s := by
    intro x
    have hx := card_normalizer_eq_eight_mul h hV x.2.1 x.2.2
    omega
  -- `s ≤ 3`
  have hsle : s ≤ 3 := by
    have hle : s ≤ Nat.card {x : G // x ∈ V ∧ x ≠ 1} := by
      rw [hs]
      calc Nat.card (Set.range (conjV V u huV hu1))
          = (Set.range (conjV V u huV hu1)).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ (Set.univ : Set {x : G // x ∈ V ∧ x ≠ 1}).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _)
        _ = Nat.card {x : G // x ∈ V ∧ x ≠ 1} := Set.ncard_univ _
    rwa [card_ne_one_of_isV4 hV] at hle
  -- `s ≥ 1`
  have hsge : 1 ≤ s := by
    have hpos : 0 < s := by
      rw [hs]
      exact (Set.ncard_pos (s := Set.range (conjV V u huV hu1))).mpr
        ⟨⟨u, huV, hu1⟩, conjV_mem_range_self huV hu1⟩
    omega
  -- `s ≠ 1`: otherwise `|N| = 8` and `C_G(u) = N` would contain `C_G(w)`
  have hsne1 : s ≠ 1 := by
    intro h1
    have hcent : Nat.card ↥(cent G u) = 8 := h.2.1 u hu2
    have hcentw : Nat.card ↥(cent G w) = 8 := h.2.1 w hw2
    have hN8 : Nat.card ↥(Subgroup.normalizer (V : Set G)) = 8 := by omega
    have hCu : cent G u ≤ Subgroup.normalizer (V : Set G) :=
      cent_le_normalizer_of_isV4 h hV huV hu1
    have hCw : cent G w ≤ Subgroup.normalizer (V : Set G) :=
      cent_le_normalizer_of_isV4 h hV hwV hw1
    have hCue : cent G u = Subgroup.normalizer (V : Set G) := by
      refine Subgroup.eq_of_le_of_card_ge hCu ?_
      omega
    have hCwe : cent G w = Subgroup.normalizer (V : Set G) := by
      refine Subgroup.eq_of_le_of_card_ge hCw ?_
      omega
    exact cent_ne_cent_of_ne h hu2 hw2 (fun hc => hwu hc.symm) (hCue.trans hCwe.symm)
  -- `s ≠ 2`: two orbits of size `2` cannot partition the three-element set
  have hsne2 : s ≠ 2 := by
    intro h2
    have hrange2 : Nat.card (Set.range (conjV V u huV hu1)) = 2 := by
      have hs' : s = Nat.card (Set.range (conjV V u huV hu1)) := hs
      omega
    -- an element outside the orbit of `u`
    obtain ⟨z, hz⟩ : ∃ z : {x : G // x ∈ V ∧ x ≠ 1}, z ∉ Set.range (conjV V u huV hu1) := by
      by_contra hcon
      push Not at hcon
      have hsub : (Set.univ : Set {x : G // x ∈ V ∧ x ≠ 1}) ⊆
          Set.range (conjV V u huV hu1) := fun y _ => hcon y
      have hle := Set.ncard_le_ncard hsub
      rw [Set.ncard_univ, card_ne_one_of_isV4 hV] at hle
      have hle' : (Set.range (conjV V u huV hu1)).ncard = 2 := by
        rw [← Nat.card_coe_set_eq, hrange2]
      omega
    -- the `z`-orbit is contained in the complement of the `u`-orbit
    have hdisj : Set.range (conjV V z.1 z.2.1 z.2.2) ⊆
        (Set.range (conjV V u huV hu1))ᶜ := by
      intro a ha
      simp only [Set.mem_compl_iff]
      intro hau
      exact hz (conjV_trans (x := ⟨u, huV, hu1⟩) (y := a) (z := z) hau (conjV_symm ha))
    have hle2 : Nat.card (Set.range (conjV V z.1 z.2.1 z.2.2)) ≤
        Nat.card ↥((Set.range (conjV V u huV hu1))ᶜ) :=
      Nat.card_le_card_of_injective
        (fun a : Set.range (conjV V z.1 z.2.1 z.2.2) =>
          (⟨a.1, hdisj a.2⟩ : ↥((Set.range (conjV V u huV hu1))ᶜ)))
        (fun a b hab => by
          have h1 : (a : {x : G // x ∈ V ∧ x ≠ 1}) = b.1 :=
            congrArg (fun z : ↥((Set.range (conjV V u huV hu1))ᶜ) =>
              (z : {x : G // x ∈ V ∧ x ≠ 1})) hab
          exact Subtype.ext h1)
    have hz2 : Nat.card (Set.range (conjV V z.1 z.2.1 z.2.2)) = 2 := by
      have h := hsize z
      omega
    have hcompl1 : Nat.card ↥((Set.range (conjV V u huV hu1))ᶜ) = 1 := by
      rw [Nat.card_coe_set_eq, Set.ncard_compl, card_ne_one_of_isV4 hV]
      have h3 : (Set.range (conjV V u huV hu1)).ncard =
          Nat.card (Set.range (conjV V u huV hu1)) := (Nat.card_coe_set_eq _).symm
      rw [h3, hrange2]
    omega
  omega


/-! ## Fixed points of the conjugation action on a Klein four group -/

/-- An element normalizing a Klein four group, with square in it and not centralizing it, fixes a
non-identity element. -/
theorem exists_fixed_of_conj_of_not_mem_centralizer {V : Subgroup G} (hV : IsV4 V) {t : G}
    (htN : t ∈ Subgroup.normalizer (V : Set G))
    (htC : t ∉ Subgroup.centralizer (V : Set G)) (ht2 : t * t ∈ V) :
    ∃ u ∈ V, u ≠ 1 ∧ t * u * t⁻¹ = u := by
  obtain ⟨v, hvV, hvt⟩ : ∃ v ∈ V, t * v * t⁻¹ ≠ v := by
    by_contra h
    push Not at h
    exact htC (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : t * y * t⁻¹ = y := h y hy
      calc y * t = (t * y * t⁻¹) * t := by rw [h1]
        _ = t * y := by group)
  have hτ2 : t * (t * v * t⁻¹) * t⁻¹ = v := by
    calc t * (t * v * t⁻¹) * t⁻¹ = (t * t) * v * (t * t)⁻¹ := by group
      _ = v := by
            rw [IsV4.comm hV ht2 hvV]
            group
  refine ⟨(t * v * t⁻¹) * v, V.mul_mem ((Subgroup.mem_normalizer_iff.mp htN v).mp hvV) hvV, ?_, ?_⟩
  · intro h1
    exact hvt (by
      calc t * v * t⁻¹ = ((t * v * t⁻¹) * v) * v⁻¹ := by group
        _ = 1 * v⁻¹ := by rw [h1]
        _ = v := by rw [one_mul, inv_eq_of_mul_eq_one_right (hV.2 v hvV)])
  · calc t * ((t * v * t⁻¹) * v) * t⁻¹
        = (t * (t * v * t⁻¹) * t⁻¹) * (t * v * t⁻¹) := by group
      _ = v * (t * v * t⁻¹) := by rw [hτ2]
      _ = (t * v * t⁻¹) * v :=
          IsV4.comm hV hvV ((Subgroup.mem_normalizer_iff.mp htN v).mp hvV)

/-- The non-identity fixed point of the conjugation action on a Klein four group is unique. -/
theorem fixed_unique_of_conj {V : Subgroup G} (hV : IsV4 V) {t u : G} (huV : u ∈ V) (hu1 : u ≠ 1)
    (hufix : t * u * t⁻¹ = u) (htN : t ∈ Subgroup.normalizer (V : Set G))
    (htC : t ∉ Subgroup.centralizer (V : Set G)) :
    ∀ v ∈ V, t * v * t⁻¹ = v → v = 1 ∨ v = u := by
  intro v hv hfix
  by_contra hcon
  push Not at hcon
  obtain ⟨hv1, hvu⟩ := hcon
  have huv1 : u * v ≠ 1 := by
    intro h1
    have h2 : u = v := by
      have h3 : u = v⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      rw [h3, inv_eq_of_mul_eq_one_right (hV.2 v hv)]
    exact hvu h2.symm
  have huvu : u * v ≠ u := by
    intro h1
    have h2 : v = 1 := by
      have h3 := congrArg (fun z : G => u * z) h1
      simpa [mul_assoc] using h3
    exact hv1 h2
  have huvv : u * v ≠ v := by
    intro h1
    have h2 : u = 1 := by
      have h3 := congrArg (fun z : G => z * v⁻¹) h1
      simpa [mul_assoc] using h3
    exact hu1 h2
  have hvs : v ≠ 1 := hv1
  have hsub : ({1, u, v, u * v} : Set G) ⊆ (V : Set G) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact huV
    · exact hv
    · exact V.mul_mem huV hv
  have hcard4 : ({1, u, v, u * v} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push Not
          exact ⟨fun h => hu1 h.symm, fun h => hvs h.symm, fun h => huv1 h.symm⟩),
      Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push Not
          exact ⟨fun h => hvu h.symm, fun h => huvu h.symm⟩),
      Set.ncard_insert_of_notMem (by
          simp only [Set.mem_singleton_iff]
          push Not
          exact fun h => huvv h.symm),
      Set.ncard_singleton]
  have hVncard : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hV.1
  have hVE : ({1, u, v, u * v} : Set G) = (V : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [hVncard, hcard4]
  -- `t` centralizes `V`
  have hcentral : t ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy4 : y ∈ ({1, u, v, u * v} : Set G) := by rw [hVE]; exact hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy4
    rcases hy4 with h | h | h | h
    · rw [h]; group
    · rw [h]
      calc u * t = (t * u * t⁻¹) * t := by rw [hufix]
        _ = t * u := by group
    · rw [h]
      calc v * t = (t * v * t⁻¹) * t := by rw [hfix]
        _ = t * v := by group
    · rw [h]
      have h1 : t * (u * v) * t⁻¹ = u * v := by
        calc t * (u * v) * t⁻¹ = (t * u * t⁻¹) * (t * v * t⁻¹) := by group
          _ = u * v := by rw [hufix, hfix]
      calc (u * v) * t = (t * (u * v) * t⁻¹) * t := by rw [h1]
        _ = t * (u * v) := by group
  exact htC hcentral

/-! ## Counting the involutions in a coset -/

/-- A subgroup of index `2` is the union of `H` and a coset `t * H`. -/
theorem exists_mul_of_mem_of_not_mem {H K : Subgroup G} (hle : H ≤ K)
    (hcard : 2 * Nat.card ↥H = Nat.card ↥K) {t z : G} (ht : t ∈ K) (htH : t ∉ H)
    (hz : z ∈ K) (hzH : z ∉ H) : ∃ w ∈ H, z = t * w := by
  have himg : ((fun w : G => t * w) '' (H : Set G)).ncard = Nat.card ↥H := by
    rw [Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)]
    exact (Nat.card_coe_set_eq (H : Set G)).symm
  have hdisj : Disjoint (H : Set G) ((fun w : G => t * w) '' (H : Set G)) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨w, hw, rfl⟩
    exact htH (by
      have h : t = (t * w) * w⁻¹ := by group
      rw [h]
      exact H.mul_mem hy (H.inv_mem hw))
  have hsub : (H : Set G) ∪ ((fun w : G => t * w) '' (H : Set G)) ⊆ (K : Set G) := by
    rintro y (hy | ⟨w, hw, rfl⟩)
    · exact hle hy
    · exact K.mul_mem ht (hle hw)
  have hunion : (H : Set G) ∪ ((fun w : G => t * w) '' (H : Set G)) = (K : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    have h := Set.ncard_union_add_ncard_inter (H : Set G) ((fun w : G => t * w) '' (H : Set G))
    rw [Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.ncard_empty, add_zero, himg] at h
    rw [show (H : Set G).ncard = Nat.card ↥H from (Nat.card_coe_set_eq _).symm] at h
    have hle2 : Nat.card ↥K ≤ Nat.card ↥H + Nat.card ↥H := by
      rw [← hcard, two_mul]
    calc (K : Set G).ncard = Nat.card ↥K := (Nat.card_coe_set_eq _).symm
      _ ≤ Nat.card ↥H + Nat.card ↥H := hle2
      _ = ((H : Set G) ∪ (fun w : G => t * w) '' (H : Set G)).ncard := h.symm
  have hzunion : z ∈ (H : Set G) ∪ ((fun w : G => t * w) '' (H : Set G)) := by
    rw [hunion]; exact hz
  rcases hzunion with hzh | ⟨w, hw, hzw⟩
  · exact absurd hzh hzH
  · exact ⟨w, hw, hzw.symm⟩

/-- A coset of a Klein four group inside the normalizer of an element of order `4`-square element
contains exactly two involutions. -/
theorem ncard_involutions_coset_eq_two {V : Subgroup G} (hV : IsV4 V) {x : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hxC : x ∉ Subgroup.centralizer (V : Set G)) (hx2 : x * x ∈ V) :
    ({y : G | y * y = 1 ∧ ∃ v ∈ V, y = x * v} : Set G).ncard = 2 := by
  obtain ⟨u, huV, hu1, hufix⟩ := exists_fixed_of_conj_of_not_mem_centralizer hV hxN hxC hx2
  have huniq : ∀ v ∈ V, x * v * x⁻¹ = v → v = 1 ∨ v = u :=
    fixed_unique_of_conj hV huV hu1 hufix hxN hxC
  have hτ : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
  have hτ2 : ∀ w ∈ V, x * (x * w * x⁻¹) * x⁻¹ = w := by
    intro w hw
    calc x * (x * w * x⁻¹) * x⁻¹ = (x * x) * w * (x * x)⁻¹ := by group
      _ = w := by
            rw [IsV4.comm hV hx2 hw]
            group
  have hsq : ∀ v ∈ V, (x * v) * (x * v) = ((x * v * x⁻¹) * v) * (x * x) := by
    intro v hv
    have hcomm : (x * x) * v = v * (x * x) := IsV4.comm hV hx2 hv
    calc (x * v) * (x * v) = ((x * v * x⁻¹) * (x * x)) * v := by group
      _ = (x * v * x⁻¹) * ((x * x) * v) := by group
      _ = (x * v * x⁻¹) * (v * (x * x)) := by rw [hcomm]
      _ = ((x * v * x⁻¹) * v) * (x * x) := by group
  have hstep : ∀ v ∈ V, ((x * (v * u) * x⁻¹) * (v * u)) = (x * v * x⁻¹) * v := by
    intro v hv
    have h1 : x * (v * u) * x⁻¹ = (x * v * x⁻¹) * u := by
      calc x * (v * u) * x⁻¹ = (x * v * x⁻¹) * (x * u * x⁻¹) := by group
        _ = (x * v * x⁻¹) * u := by rw [hufix]
    rw [h1]
    have hcomm : u * v = v * u := IsV4.comm hV huV hv
    calc ((x * v * x⁻¹) * u) * (v * u) = (x * v * x⁻¹) * (u * (v * u)) := by group
      _ = (x * v * x⁻¹) * (u * (u * v)) := by rw [hcomm]
      _ = (x * v * x⁻¹) * v := by
            rw [show u * (u * v) = v from by rw [← mul_assoc, hV.2 u huV, one_mul]]
  -- the equation characterising the solutions
  have hsols : ∀ v ∈ V, (x * v) * (x * v) = 1 ↔ (x * v * x⁻¹) * v = x * x := by
    intro v hv
    rw [hsq v hv]
    constructor
    · intro h1
      have h2 : (x * v * x⁻¹) * v = (x * x)⁻¹ := by
        calc (x * v * x⁻¹) * v = ((x * v * x⁻¹) * v) * ((x * x) * (x * x)⁻¹) := by group
          _ = (((x * v * x⁻¹) * v) * (x * x)) * (x * x)⁻¹ := by group
          _ = 1 * (x * x)⁻¹ := by rw [h1]
          _ = (x * x)⁻¹ := one_mul _
      rwa [inv_eq_of_mul_eq_one_right (hV.2 (x * x) hx2)] at h2
    · intro h1
      rw [h1]
      exact hV.2 (x * x) hx2
  -- the fibre structure of the map `v ↦ τ(v) v` on `V`
  have hkey : ∀ v ∈ V, ∀ w ∈ V, (x * v * x⁻¹) * v = (x * w * x⁻¹) * w →
      v * w = x * (v * w) * x⁻¹ := by
    intro v hv w hw heq
    have hτwsq : (x * w * x⁻¹) * (x * w * x⁻¹) = 1 := by
      calc (x * w * x⁻¹) * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
        _ = 1 := by rw [hV.2 w hw]; group
    have hstar : (x * w * x⁻¹) * ((x * v * x⁻¹) * v) = w := by
      rw [heq, ← mul_assoc, hτwsq, one_mul]
    have hcomm1 : (x * w * x⁻¹) * (x * v * x⁻¹) = w * v := by
      calc (x * w * x⁻¹) * (x * v * x⁻¹)
          = (x * w * x⁻¹) * ((x * v * x⁻¹) * (v * v)) := by rw [hV.2 v hv, mul_one]
        _ = (x * w * x⁻¹) * (((x * v * x⁻¹) * v) * v) := by group
        _ = ((x * w * x⁻¹) * ((x * v * x⁻¹) * v)) * v := by group
        _ = w * v := by rw [hstar]
    calc v * w = (x * v * x⁻¹) * (x * w * x⁻¹) := by
          rw [IsV4.comm hV (hτ v hv) (hτ w hw), hcomm1, IsV4.comm hV hw hv]
      _ = x * (v * w) * x⁻¹ := by group
  have hstepinv : ∀ v ∈ V, ∀ w ∈ V, (x * v * x⁻¹) * v = (x * w * x⁻¹) * w →
      w = v ∨ w = v * u := by
    intro v hv w hw heq
    have h1 : v * w = x * (v * w) * x⁻¹ := hkey v hv w hw heq
    have h2 : v * w ∈ V := V.mul_mem hv hw
    rcases huniq (v * w) h2 h1.symm with h3 | h3
    · left
      calc w = v * (v * w) := by rw [← mul_assoc, hV.2 v hv, one_mul]
        _ = v * 1 := by rw [h3]
        _ = v := mul_one v
    · right
      calc w = v * (v * w) := by rw [← mul_assoc, hV.2 v hv, one_mul]
        _ = v * u := by rw [h3]
  -- a solution exists
  have hsol : ∃ v₀ ∈ V, (x * v₀ * x⁻¹) * v₀ = x * x := by
    have hx2fix : x * (x * x) * x⁻¹ = x * x := by group
    rcases huniq (x * x) hx2 hx2fix with h1 | h1
    · refine ⟨1, V.one_mem, ?_⟩
      rw [h1]; group
    · obtain ⟨v₁, hv1, hv1'⟩ : ∃ v ∈ V, x * v * x⁻¹ ≠ v := by
        by_contra hcon
        push Not at hcon
        exact hxC (by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          calc y * x = (x * y * x⁻¹) * x := by rw [hcon y hy]
            _ = x * y := by group)
      refine ⟨v₁, hv1, ?_⟩
      have hfix : x * ((x * v₁ * x⁻¹) * v₁) * x⁻¹ = (x * v₁ * x⁻¹) * v₁ := by
        calc x * ((x * v₁ * x⁻¹) * v₁) * x⁻¹
            = (x * (x * v₁ * x⁻¹) * x⁻¹) * (x * v₁ * x⁻¹) := by group
          _ = v₁ * (x * v₁ * x⁻¹) := by rw [hτ2 v₁ hv1]
          _ = (x * v₁ * x⁻¹) * v₁ := IsV4.comm hV hv1 (hτ v₁ hv1)
      have hmem : (x * v₁ * x⁻¹) * v₁ ∈ V := V.mul_mem (hτ v₁ hv1) hv1
      have hne : (x * v₁ * x⁻¹) * v₁ ≠ 1 := by
        intro hc
        apply hv1'
        calc x * v₁ * x⁻¹ = ((x * v₁ * x⁻¹) * v₁) * v₁⁻¹ := by group
          _ = 1 * v₁⁻¹ := by rw [hc]
          _ = v₁ := by rw [one_mul, inv_eq_of_mul_eq_one_right (hV.2 v₁ hv1)]
      rcases huniq ((x * v₁ * x⁻¹) * v₁) hmem hfix with h2 | h2
      · exact absurd h2 hne
      · rw [h2, h1]
  obtain ⟨v₀, hv0V, hv0φ⟩ := hsol
  -- the solution set is `{v₀, v₀ * u}`
  have hS : ({v : G | v ∈ V ∧ (x * v * x⁻¹) * v = x * x} : Set G) = {v₀, v₀ * u} := by
    ext v
    constructor
    · rintro ⟨hv, hvv⟩
      rcases hstepinv v₀ hv0V v hv (by rw [hv0φ, hvv]) with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with h | h
      · rw [h]; exact ⟨hv0V, hv0φ⟩
      · rw [h]; exact ⟨V.mul_mem hv0V huV, by rw [hstep v₀ hv0V, hv0φ]⟩
  -- the set of involutions in the coset
  have hseteq : ({y : G | y * y = 1 ∧ ∃ v ∈ V, y = x * v} : Set G) =
      (fun v : G => x * v) '' ({v : G | v ∈ V ∧ (x * v * x⁻¹) * v = x * x} : Set G) := by
    ext y
    constructor
    · rintro ⟨hy2, v, hv, rfl⟩
      exact ⟨v, ⟨hv, (hsols v hv).mp hy2⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hvv⟩, rfl⟩
      exact ⟨(hsols v hv).mpr hvv, v, hv, rfl⟩
  rw [hseteq, Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab), hS]
  have hne : v₀ ≠ v₀ * u := by
    intro h1
    have h3 := congrArg (fun z : G => v₀⁻¹ * z) h1
    have h2 : u = 1 := by simpa [mul_assoc] using h3.symm
    exact hu1 h2
  rw [Set.ncard_insert_of_notMem (by simpa [Set.mem_singleton_iff] using hne),
    Set.ncard_singleton]


/-- The normalizer of a Klein four group contains exactly nine involutions. -/
theorem card_involutions_normalizer (h : K4Hyp G) {V : Subgroup G} (hV : IsV4 V) :
    ({x : G | orderOf x = 2 ∧ x ∈ Subgroup.normalizer (V : Set G)} : Set G).ncard = 9 := by
  classical
  have hCV : Subgroup.centralizer (V : Set G) = V := centralizer_eq_self_of_isV4 h hV
  have hVN : V ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer
  have hAcard : Nat.card {x : G // orderOf x = 2 ∧ x ∈ Subgroup.normalizer (V : Set G)} = 9 := by
    have hsplit : Nat.card {x : G // orderOf x = 2 ∧ x ∈ Subgroup.normalizer (V : Set G)} =
        Nat.card {x : {x : G // orderOf x = 2 ∧ x ∈ Subgroup.normalizer (V : Set G)} //
            (x.1 : G) ∈ V} +
          Nat.card {x : {x : G // orderOf x = 2 ∧ x ∈ Subgroup.normalizer (V : Set G)} //
            ¬((x.1 : G) ∈ V)} := by
      rw [← Nat.card_sum]
      exact Nat.card_congr (Equiv.sumCompl
        (fun x : {x : G // orderOf x = 2 ∧ x ∈ Subgroup.normalizer (V : Set G)} =>
          (x.1 : G) ∈ V)).symm
    -- the involutions inside `V`
    have hAV : Nat.card {x : {x : G // orderOf x = 2 ∧ x ∈ Subgroup.normalizer (V : Set G)} //
        (x.1 : G) ∈ V} = 3 := by
      have hbij : Nat.card {x : {x : G // orderOf x = 2 ∧
            x ∈ Subgroup.normalizer (V : Set G)} // (x.1 : G) ∈ V} =
          Nat.card {x : G // x ∈ V ∧ x ≠ 1} := Nat.card_congr {
        toFun := fun x => ⟨x.1.1, x.2, fun hc => by
          have h2 := x.1.2.1
          rw [hc, orderOf_one] at h2
          exact absurd h2 (by norm_num)⟩
        invFun := fun x => ⟨⟨x.1, hV.orderOf_eq_two x.2.1 x.2.2, hVN x.2.1⟩, x.2.1⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
      rw [hbij, card_ne_one_of_isV4 hV]
    -- the involutions outside `V`, partitioned by their fixed point
    have hex : ∀ x : {x : {x : G // orderOf x = 2 ∧
          x ∈ Subgroup.normalizer (V : Set G)} // ¬((x.1 : G) ∈ V)},
        ∃ w : G, w ∈ V ∧ w ≠ 1 ∧ x.1.1 * w * x.1.1⁻¹ = w := by
      intro x
      have hx2 : orderOf (x.1.1 : G) = 2 := x.1.2.1
      have hxsq : (x.1.1 : G) * (x.1.1 : G) ∈ V := by
        have h1 : (x.1.1 : G) ^ 2 = 1 := by
          simpa [hx2] using pow_orderOf_eq_one (x.1.1 : G)
        rw [pow_two] at h1
        rw [h1]
        exact V.one_mem
      exact exists_fixed_of_conj_of_not_mem_centralizer hV x.1.2.2 (by rw [hCV]; exact x.2) hxsq
    let ψ : {x : {x : G // orderOf x = 2 ∧
          x ∈ Subgroup.normalizer (V : Set G)} // ¬((x.1 : G) ∈ V)} →
        {w : G // w ∈ V ∧ w ≠ 1} := fun x =>
      ⟨(hex x).choose, (hex x).choose_spec.1, (hex x).choose_spec.2.1⟩
    have hψfix : ∀ x : {x : {x : G // orderOf x = 2 ∧
          x ∈ Subgroup.normalizer (V : Set G)} // ¬((x.1 : G) ∈ V)},
        x.1.1 * (ψ x).1 * x.1.1⁻¹ = (ψ x).1 := fun x => (hex x).choose_spec.2.2
    have hAout : Nat.card {x : {x : G // orderOf x = 2 ∧
          x ∈ Subgroup.normalizer (V : Set G)} // ¬((x.1 : G) ∈ V)} = 6 := by
      have hfib : ∀ w : {w : G // w ∈ V ∧ w ≠ 1},
          Nat.card {x : {x : {x : G // orderOf x = 2 ∧
              x ∈ Subgroup.normalizer (V : Set G)} // ¬((x.1 : G) ∈ V)} // ψ x = w} = 2 := by
        intro w
        have hw2 : orderOf (w.1 : G) = 2 := hV.orderOf_eq_two w.2.1 w.2.2
        have hcent8 : Nat.card ↥(cent G (w.1 : G)) = 8 := h.2.1 w.1 hw2
        have hcardcent : 2 * Nat.card ↥V = Nat.card ↥(cent G (w.1 : G)) := by
          rw [hV.1, hcent8]
        -- an element of `C_G(w) \ V`
        obtain ⟨t, htcent, htV⟩ : ∃ t : G, t ∈ cent G (w.1 : G) ∧ t ∉ V := by
          by_contra hcon
          push Not at hcon
          have hle : cent G (w.1 : G) ≤ V := fun z hz => hcon z hz
          have hle' := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
            (Subgroup.inclusion_injective hle)
          rw [hcent8, hV.1] at hle'
          omega
        have htN : t ∈ Subgroup.normalizer (V : Set G) :=
          cent_le_normalizer_of_isV4 h hV w.2.1 w.2.2 htcent
        have htC : t ∉ Subgroup.centralizer (V : Set G) := by rw [hCV]; exact htV
        have ht2 : t * t ∈ V := by
          by_contra hcon
          have hmem : t * t ∈ cent G (w.1 : G) := (cent G w.1).mul_mem htcent htcent
          obtain ⟨v, hv, hv'⟩ := exists_mul_of_mem_of_not_mem (H := V) (K := cent G (w.1 : G))
            (hV.le_cent w.2.1) hcardcent htcent htV hmem hcon
          have ht_eq : t = v := by
            have h4 : t⁻¹ * (t * t) = t⁻¹ * (t * v) := by rw [hv']
            simpa [mul_assoc] using h4
          exact htV (ht_eq ▸ hv)
        -- the fibre over `w` is the set of involutions in the coset `t * V`
        have hD3 : ({y : G | y * y = 1 ∧ ∃ v ∈ V, y = t * v} : Set G).ncard = 2 :=
          ncard_involutions_coset_eq_two hV htN htC ht2
        have hD3' : Nat.card {y : G // y * y = 1 ∧ ∃ v ∈ V, y = t * v} = 2 :=
          (Nat.card_coe_set_eq {y : G | y * y = 1 ∧ ∃ v ∈ V, y = t * v}).trans hD3
        -- the backward map
        have hbwd : ∀ y : G, y * y = 1 → (∃ v ∈ V, y = t * v) →
            ∃ X : {x : {x : {x : G // orderOf x = 2 ∧
                x ∈ Subgroup.normalizer (V : Set G)} // ¬((x.1 : G) ∈ V)} // ψ x = w},
              y = X.1.1.1 := by
          intro y hy2 hyv
          obtain ⟨v, hv, hyv'⟩ := hyv
          have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
            rw [hyv']
            exact (Subgroup.normalizer (V : Set G)).mul_mem htN (hVN hv)
          have hyV : y ∉ V := by
            intro hc
            refine htV ?_
            have h3 : t = y * v⁻¹ := by rw [hyv']; group
            rw [h3]
            exact V.mul_mem hc (V.inv_mem hv)
          have hy1 : y ≠ 1 := by
            intro hc
            refine htV ?_
            have h4 : t * v = 1 := by rw [← hyv', hc]
            rw [mul_eq_one_iff_eq_inv.mp h4]
            exact V.inv_mem hv
          have hyord : orderOf y = 2 := by
            refine orderOf_eq_prime ?_ hy1
            rw [pow_two]; exact hy2
          have hycent : y ∈ cent G (w.1 : G) := by
            rw [hyv']
            exact (cent G (w.1 : G)).mul_mem htcent (hV.le_cent w.2.1 hv)
          have hyfixw : y * (w.1 : G) * y⁻¹ = (w.1 : G) := by
            rw [Subgroup.mem_centralizer_singleton_iff] at hycent
            calc y * (w.1 : G) * y⁻¹ = ((w.1 : G) * y) * y⁻¹ := by rw [hycent]
              _ = (w.1 : G) := by group
          have hfix := hψfix ⟨⟨y, ⟨hyord, hyN⟩⟩, hyV⟩
          have hC' : y ∉ Subgroup.centralizer (V : Set G) := by rw [hCV]; exact hyV
          have hwval : (ψ ⟨⟨y, ⟨hyord, hyN⟩⟩, hyV⟩).1 = (w.1 : G) := by
            rcases fixed_unique_of_conj hV (ψ ⟨⟨y, ⟨hyord, hyN⟩⟩, hyV⟩).2.1
              (ψ ⟨⟨y, ⟨hyord, hyN⟩⟩, hyV⟩).2.2 hfix hyN hC' (w.1 : G) w.2.1 hyfixw with h | h
            · exact absurd h w.2.2
            · exact h.symm
          exact ⟨⟨⟨⟨y, ⟨hyord, hyN⟩⟩, hyV⟩, Subtype.ext hwval⟩, rfl⟩
        let toF : {x : {x : {x : G // orderOf x = 2 ∧
              x ∈ Subgroup.normalizer (V : Set G)} // ¬((x.1 : G) ∈ V)} // ψ x = w} →
            {y : G // y * y = 1 ∧ ∃ v ∈ V, y = t * v} := fun x =>
          ⟨x.1.1.1, by
            have h1 : (x.1.1.1 : G) ^ 2 = 1 := by
              simpa [x.1.1.2.1] using pow_orderOf_eq_one (x.1.1.1 : G)
            rwa [pow_two] at h1, by
            have hcomm : (x.1.1.1 : G) ∈ cent G (w.1 : G) := by
              have hfix := hψfix x.1
              rw [x.2] at hfix
              rw [Subgroup.mem_centralizer_singleton_iff]
              calc (x.1.1.1 : G) * (w.1 : G)
                  = ((x.1.1.1 : G) * (w.1 : G) * (x.1.1.1 : G)⁻¹) * (x.1.1.1 : G) := by group
                _ = (w.1 : G) * (x.1.1.1 : G) := by rw [hfix]
            exact exists_mul_of_mem_of_not_mem (H := V) (K := cent G (w.1 : G))
              (hV.le_cent w.2.1) hcardcent htcent htV hcomm x.1.2⟩
        have hbij : Nat.card {x : {x : {x : G // orderOf x = 2 ∧
              x ∈ Subgroup.normalizer (V : Set G)} // ¬((x.1 : G) ∈ V)} // ψ x = w} =
            Nat.card {y : G // y * y = 1 ∧ ∃ v ∈ V, y = t * v} :=
          Nat.card_congr {
            toFun := toF
            invFun := fun y => (hbwd y.1 y.2.1 y.2.2).choose
            left_inv := fun x => by
              have h := (hbwd (toF x).1 (toF x).2.1 (toF x).2.2).choose_spec
              have h2 : ((hbwd (toF x).1 (toF x).2.1 (toF x).2.2).choose).1.1.1
                  = x.1.1.1 := by
                rw [← h]
              exact Subtype.ext (Subtype.ext (Subtype.ext h2))
            right_inv := fun y => by
              have h := (hbwd y.1 y.2.1 y.2.2).choose_spec
              have h2 : (toF ((hbwd y.1 y.2.1 y.2.2).choose)).1 = y.1 := by
                dsimp only [toF]
                exact h.symm
              exact Subtype.ext h2 }
        rw [hbij, hD3']
      have h1 := Work.COPR.card_mul_of_fibers ψ 2 hfib
      rw [h1, card_ne_one_of_isV4 hV]
    rw [hsplit, hAV, hAout]
  rw [← Nat.card_coe_set_eq]
  exact hAcard
end Setup

theorem fourGroupNormalizer {G : Type} [Group G] [Finite G] (h : Work.BSW.Cases.K4.K4Hyp G)
    (V : Subgroup G) (hV : Work.BSW.Cases.K4.IsV4 V) :
    Subgroup.centralizer (V : Set G) = V ∧
    Nat.card ↥(Subgroup.normalizer (V : Set G)) = 24 ∧
    ({x : G | orderOf x = 2 ∧ x ∈ Subgroup.normalizer (V : Set G)} : Set G).ncard = 9 :=
  ⟨centralizer_eq_self_of_isV4 h hV, card_normalizer_eq h hV, card_involutions_normalizer h hV⟩

end Work.BSW.Cases.K4
