import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.CosetInvCountLeSix

/-!
# Bender 1981 §3 (6) + (7) ⟹ `n ≠ 6`

This file assembles `cosetInvCount B.Hhat y ≠ 6` from the two steps of Bender's §3:

* **Bender (6)** (`hSix`): if the coset of the involution `y ∉ Ĥ` carries at least five
  involutions, then some involution `z` of the same coset inverts a nontrivial odd-order
  subgroup `X ≤ Ĥ` whose centralizer and normalizer in `G` have even order;
* **Bender (7)** (`hSeven`): for such an involution `z` and subgroup `X`, `|U| = 3` and
  `|Ĥ ⊓ Ĥ^z| = 6`.

The contradiction is then elementary.  If `n = |I_Ĥ(z)| = 6` (the coset count is a coset
invariant), then `I_Ĥ(z)` has six elements and is contained in `D := Ĥ ⊓ Ĥ^z`, which also has
six elements; hence `I_Ĥ(z) = D` as sets, so `D` is closed under multiplication.  But `z`
inverts every element of `I_Ĥ(z) = D`, and multiplicativity of conjugation gives
`a⁻¹ b⁻¹ = (ab)⁻¹ = b⁻¹ a⁻¹` for `a, b ∈ D`, so `D` is abelian.  An abelian group of order
`6` contains an element `x` of order `6`; since `x ∈ I_Ĥ(z)`, the orders of `x` and of its image
in `Ĥ/VU` agree (Bender (5): `x^m ∈ I_Ĥ(z) ∩ VU = {1}` for `m = orderOf (x·VU)`), so `Ĥ/VU`
— of order `6` — has an element of order `6`, hence is abelian, contradicting Bender's
Theorem 2.6 (which makes `Ĥ/VU` nonabelian).
-/

namespace Work.CORE3

open Work.GW2
open Subgroup

variable {G : Type} [Group G]

/-- `h ↦ h * h0⁻¹` is a bijection `I_Hh(y) → I_Hh(h0 * y)` when `h0 ∈ Hh`, `y` is an involution
and `h0 * y` is an involution. -/
theorem ncard_invSetIn_mul_eq (Hh : Subgroup G) {h0 y : G} (hh0 : h0 ∈ Hh)
    (hy : y * y = 1) (hz : (h0 * y) * (h0 * y) = 1) :
    (invSetIn Hh (h0 * y)).ncard = (invSetIn Hh y).ncard := by
  refine (Set.ncard_congr (s := invSetIn Hh y) (t := invSetIn Hh (h0 * y))
    (fun h _ => h * h0⁻¹) ?_ ?_ ?_).symm
  · intro h hh
    obtain ⟨hhH, hhy⟩ := hh
    refine ⟨Hh.mul_mem hhH (Hh.inv_mem hh0), ?_⟩
    calc (h0 * y) * (h * h0⁻¹) * (h0 * y) = h0 * (y * h * y) := by group
      _ = h0 * h⁻¹ := by rw [hhy]
      _ = (h * h0⁻¹)⁻¹ := by group
  · intro a b _ _ hab
    have h := congrArg (fun w => w * h0) hab
    simpa [mul_assoc] using h
  · intro b hb
    obtain ⟨hbH, hby⟩ := hb
    refine ⟨b * h0, ?_, ?_⟩
    · refine ⟨Hh.mul_mem hbH hh0, ?_⟩
      have h := congrArg (fun w => h0⁻¹ * w) hby
      calc y * (b * h0) * y = h0⁻¹ * ((h0 * y) * b * (h0 * y)) := by group
        _ = h0⁻¹ * b⁻¹ := h
        _ = (b * h0)⁻¹ := by group
    · group

/-- **Bender (6) + (7) ⟹ `n ≠ 6`.**  Given the two steps as hypotheses, no coset of `Ĥ`
containing an involution `y ∉ Ĥ` contains exactly six involutions. -/
theorem cosetInvCount_ne_six_of (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (h : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1})
    (hSix : ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → 5 ≤ cosetInvCount B.Hhat y →
      ∃ z : G, orderOf z = 2 ∧ (∃ k ∈ B.Hhat, z = k * y) ∧
        ∃ X : Subgroup G, X ≤ B.Hhat ∧ X ≠ ⊥ ∧ Odd (Nat.card ↥X) ∧ Inverts z X ∧
          Even (Nat.card (centralizer (X : Set G))) ∧
          Even (Nat.card (normalizer (X : Set G))) ∧
          (∃ s ∈ B.Hhat, orderOf s = 2 ∧ Inverts s X))
    (hSeven : ∀ (y : G) (X : Subgroup G), orderOf y = 2 → y ∉ B.Hhat → X ≤ B.Hhat → X ≠ ⊥ →
      Odd (Nat.card ↥X) → Inverts y X → Even (Nat.card (centralizer (X : Set G))) →
      Even (Nat.card (normalizer (X : Set G))) →
      {s : G} → s ∈ B.Hhat → orderOf s = 2 → Inverts s X →
      Nat.card B.U = 3 ∧ Nat.card ↥(B.Hhat ⊓ conjSub y B.Hhat) = 6) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → cosetInvCount B.Hhat y ≠ 6 := by
  intro y hy2 hyH hcnt6
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  obtain ⟨z, hz2, ⟨h0, hh0, hz0⟩, X, hXle, hXne, hXodd, hinv, hCe, hNe, s, hsH, hs2, hsX⟩ :=
    hSix y hy2 hyH (by omega)
  have hy : y * y = 1 := (orderOf_eq_two_iff_mul_self y).mp hy2 |>.1
  have hz : z * z = 1 := (orderOf_eq_two_iff_mul_self z).mp hz2 |>.1
  have hzH : z ∉ B.Hhat := by
    rintro hzmem
    refine hyH ?_
    have hyz : y = h0⁻¹ * z := by rw [hz0]; group
    rw [hyz]
    exact B.Hhat.mul_mem (B.Hhat.inv_mem hh0) hzmem
  obtain ⟨hU3, hD6⟩ := hSeven z X hz2 hzH hXle hXne hXodd hinv hCe hNe (s := s) hsH hs2 hsX
  -- the coset count is a coset invariant
  have hcnt_eq : cosetInvCount B.Hhat z = cosetInvCount B.Hhat y := by
    rw [← ncard_invSetIn_eq_cosetInvCount B.Hhat z hz hzH,
      ← ncard_invSetIn_eq_cosetInvCount B.Hhat y hy hyH]
    have hlem := ncard_invSetIn_mul_eq B.Hhat hh0 hy (by rw [← hz0]; exact hz)
    simpa [hz0] using hlem
  have hzcnt : (invSetIn B.Hhat z).ncard = 6 := by
    rw [ncard_invSetIn_eq_cosetInvCount B.Hhat z hz hzH, hcnt_eq]
    exact hcnt6
  -- `D = Ĥ ⊓ Ĥ^z`
  let DD : Subgroup G := B.Hhat ⊓ conjSub z B.Hhat
  have hD6' : Nat.card ↥DD = 6 := hD6
  have hIle : (invSetIn B.Hhat z : Set G) ⊆ (DD : Set G) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    show x ∈ conjSub z B.Hhat
    refine (Work.CORE2A.mem_conjSub_iff (g := z) (K := B.Hhat)).mpr ?_
    rw [inv_eq_of_mul_eq_one_right hz, hx.2]
    exact B.Hhat.inv_mem hx.1
  have hDcard : (DD : Set G).ncard = 6 := by
    rw [← Nat.card_coe_set_eq]; exact hD6'
  have hIeq : (invSetIn B.Hhat z : Set G) = (DD : Set G) :=
    Set.eq_of_subset_of_ncard_le hIle (by rw [hDcard, hzcnt])
  have hmem : ∀ x : G, x ∈ (invSetIn B.Hhat z : Set G) ↔ x ∈ (DD : Set G) := fun x => by
    rw [hIeq]
  -- `I_Ĥ(z) ⊓ VU = 1`
  have hIVU : ∀ x : G, x ∈ invSetIn B.Hhat z → x ∈ (pCoreIn 2 B.Hhat ⊔ B.U) → x = 1 := by
    intro x hx hxVU
    have hz5 := h5 z hz2 hzH
    have hmem' : x ∈ invSet (pCoreIn 2 B.Hhat ⊔ B.U) z := by
      refine ⟨hxVU, ?_⟩
      rw [inv_eq_of_mul_eq_one_right hz]
      exact hx.2
    rw [hz5] at hmem'
    exact Set.mem_singleton_iff.mp hmem'
  -- `D` is abelian
  have hDab : ∀ a ∈ (DD : Set G), ∀ b ∈ (DD : Set G), a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ invSetIn B.Hhat z := (hmem a).mpr ha
    have hb' : b ∈ invSetIn B.Hhat z := (hmem b).mpr hb
    have hab' : a * b ∈ invSetIn B.Hhat z := (hmem (a * b)).mpr (DD.mul_mem ha hb)
    have h2 : (z * a * z) * (z * b * z) = z * (a * b) * z := by
      rw [show (z * a * z) * (z * b * z) = z * a * (z * z) * b * z from by group, hz]
      group
    rw [ha'.2, hb'.2, hab'.2] at h2
    have h3 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by rw [h2, mul_inv_rev]
    have h4 := congrArg Inv.inv h3
    simp only [mul_inv_rev, inv_inv] at h4
    exact h4.symm
  -- an element of order `6` in `D`
  obtain ⟨a, haord⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hD6']; norm_num)
  obtain ⟨b, hbord⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hD6']; norm_num)
  have hab : Commute a b := Subtype.ext (hDab (a : G) a.2 (b : G) b.2)
  have hx6 : orderOf (a * b) = 6 := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hab (by rw [haord, hbord]; norm_num),
      haord, hbord]
  have hxI : (((a * b : ↥DD)) : G) ∈ invSetIn B.Hhat z := (hmem _).mpr ((a * b : ↥DD).2)
  have hx6G : orderOf (((a * b : ↥DD)) : G) = 6 := by
    rw [Subgroup.orderOf_coe]; exact hx6
  have hxH : (((a * b : ↥DD)) : G) ∈ B.Hhat :=
    (Subgroup.mem_inf.mp (show (((a * b : ↥DD)) : G) ∈ B.Hhat ⊓ conjSub z B.Hhat from
      ((a * b : ↥DD)).2)).1
  have hx6H : orderOf (⟨(((a * b : ↥DD)) : G), hxH⟩ : ↥B.Hhat) = 6 := by
    rw [Subgroup.orderOf_mk]; exact hx6G
  -- the quotient `Ĥ/VU`
  have hWn : ((pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat).Normal :=
    normal_VU_subgroupOf G I h B h1 D
  let N : Subgroup ↥B.Hhat := (pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat
  haveI : N.Normal := hWn
  have hcard6 : Nat.card (↥B.Hhat ⧸ N) = 6 := by
    rw [← Subgroup.index_eq_card N]
    exact relIndex_VU_Hhat G I h B h1 D
  have hQnab : ¬ IsMulCommutative (↥B.Hhat ⧸ N) := by
    intro hc
    have hnab0 : ∃ u ∈ B.Hhat, ∃ v ∈ B.Hhat,
        u * v * u⁻¹ * v⁻¹ ∉ (pCoreIn 2 B.Hhat ⊔ B.U) := by
      rcases h26.2.2 with ⟨hle, -⟩ | ⟨-, -, hnab⟩
      · exact absurd (isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
          (not_isCyclic_of_isFourGroup' D.four)
      · exact hnab
    obtain ⟨u, hu, v, hv, hcomm⟩ := hnab0
    apply hcomm
    have hcy := (isMulCommutative_iff.mp hc)
      (QuotientGroup.mk' N (⟨u, hu⟩ : ↥B.Hhat)) (QuotientGroup.mk' N (⟨v, hv⟩ : ↥B.Hhat))
    have h1 : QuotientGroup.mk' N
        ((⟨u, hu⟩ : ↥B.Hhat) * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcy]
      group
    have hN : ((⟨u, hu⟩ : ↥B.Hhat) * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹) ∈ N := by
      rw [← QuotientGroup.ker_mk' (N := N)]
      exact MonoidHom.mem_ker.mpr h1
    have hmem' := Subgroup.mem_subgroupOf.mp hN
    simpa [N] using hmem'
  -- `orderOf (x · VU) = orderOf x = 6`
  set m : ℕ := orderOf (QuotientGroup.mk (⟨(((a * b : ↥DD)) : G), hxH⟩ : ↥B.Hhat) :
    ↥B.Hhat ⧸ N) with hm_def
  have hm_dvd : m ∣ 6 := by
    rw [hm_def, ← hx6H]
    exact orderOf_map_dvd (QuotientGroup.mk' N) _
  have hx_pow : (⟨(((a * b : ↥DD)) : G), hxH⟩ : ↥B.Hhat) ^ m ∈ N := by
    have h1 : QuotientGroup.mk' N ((⟨(((a * b : ↥DD)) : G), hxH⟩ : ↥B.Hhat) ^ m) = 1 := by
      rw [map_pow]
      exact pow_orderOf_eq_one _
    rw [← QuotientGroup.ker_mk' (N := N)]
    exact MonoidHom.mem_ker.mpr h1
  have hx_m_VU : (((⟨(((a * b : ↥DD)) : G), hxH⟩ : ↥B.Hhat) ^ m : ↥B.Hhat) : G)
      ∈ (pCoreIn 2 B.Hhat ⊔ B.U) := by
    have hh := Subgroup.mem_subgroupOf.mp hx_pow
    simpa [N] using hh
  have hx_m_I : (((⟨(((a * b : ↥DD)) : G), hxH⟩ : ↥B.Hhat) ^ m : ↥B.Hhat) : G)
      ∈ invSetIn B.Hhat z := by
    have hh := pow_mem_invSetIn (Hh := B.Hhat) (y := z) hz hxI m
    simpa using hh
  have hx_m_one : (((⟨(((a * b : ↥DD)) : G), hxH⟩ : ↥B.Hhat) ^ m : ↥B.Hhat) : G) = 1 :=
    hIVU _ hx_m_I hx_m_VU
  have h6_dvd : 6 ∣ m := by
    rw [← hx6H]
    exact orderOf_dvd_iff_pow_eq_one.mpr
      (Subtype.ext (by simpa using hx_m_one))
  have hm_eq : m = 6 := Nat.dvd_antisymm hm_dvd h6_dvd
  -- the quotient is cyclic, hence abelian
  have hcyc : IsCyclic (↥B.Hhat ⧸ N) := by
    refine isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨QuotientGroup.mk (⟨(((a * b : ↥DD)) : G), hxH⟩ : ↥B.Hhat), ?_⟩
    refine Subgroup.eq_top_of_card_eq (H := Subgroup.zpowers _) ?_
    rw [Nat.card_zpowers, ← hm_def, hm_eq, hcard6]
  exact hQnab (IsMulCommutative.of_comm (fun p q => by
    letI := IsCyclic.commGroup (α := ↥B.Hhat ⧸ N)
    exact mul_comm p q))

end Work.CORE3
