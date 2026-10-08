import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Quaternion.tau_zpow_mem_zpowers_two_four
import Submission.Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow
import Submission.Work.NPC.All
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.BrauerSuzuki.Dade.zpowers_sup_of_commute_coprime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Dade

open Classical

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

/-! ## Elementary facts about the generalized quaternion Sylow `2`-subgroup -/

/-- `τ`, the element of `S` of order `2 ^ n`, has order `2 ^ n` in `G`. -/
lemma orderOf_tau_coe (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    orderOf ((d.tau : ↥S) : G) = 2 ^ d.n := by
  rw [Subgroup.orderOf_coe]
  exact d.tau_order

/-- The order of `τ ^ 2` in `G` is `2 ^ (n - 1)`. -/
lemma tau_sq_order (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    orderOf (((d.tau : ↥S) : G) ^ 2) = 2 ^ (d.n - 1) := by
  rw [orderOf_pow, orderOf_tau_coe]
  have hn1 : 1 ≤ d.n := by have := d.hn; omega
  have hgcd : Nat.gcd (2 ^ d.n) 2 = 2 :=
    Nat.gcd_eq_right (dvd_trans (dvd_refl 2) (pow_dvd_pow 2 hn1))
  rw [hgcd, show 2 ^ d.n = 2 ^ (d.n - 1) * 2 from by
    rw [← pow_succ]; congr 1; omega]
  exact Nat.mul_div_cancel _ (by norm_num)

/-- `τ ^ 4 ≠ 1` for `n ≥ 3`. -/
lemma tau_pow_four_ne_one (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : (((d.tau : ↥S) : G)) ^ 4 ≠ 1 := by
  intro h
  have hdvd : (2 : ℕ) ^ d.n ∣ 4 := by
    rw [← orderOf_tau_coe]
    exact orderOf_dvd_iff_pow_eq_one.mpr h
  have hle : 2 ^ d.n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have h8 : 8 ≤ 2 ^ d.n := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ d.n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- `τ ^ 2 ≠ 1` for `n ≥ 3`. -/
lemma tau_sq_ne_one (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : (((d.tau : ↥S) : G)) ^ 2 ≠ 1 := by
  intro h
  have hdvd : (2 : ℕ) ^ d.n ∣ 2 := by
    rw [← orderOf_tau_coe]
    exact orderOf_dvd_iff_pow_eq_one.mpr h
  have hle : 2 ^ d.n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h8 : 8 ≤ 2 ^ d.n := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ d.n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- `τ` centralizes `τ ^ 2`. -/
lemma tau_mem_centralizer (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    ((d.tau : ↥S) : G) ∈ Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hle : Subgroup.zpowers ((((d.tau : ↥S) : G)) ^ 2) ≤
      Subgroup.centralizer ({(((d.tau : ↥S) : G))} : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    group
  have := hle hh
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

/-- `ρ` normalizes `⟨τ ^ 2⟩`. -/
lemma rho_mem_normalizer (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    ((d.rho : ↥S) : G) ∈ Subgroup.normalizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) := by
  have hconj : ((d.rho : ↥S) : G) * (((d.tau : ↥S) : G)) * (((d.rho : ↥S) : G))⁻¹ =
      (((d.tau : ↥S) : G))⁻¹ := by
    have := congrArg (Subtype.val) d.rho_conj
    simpa using this
  have hconj2 : ((d.rho : ↥S) : G) * ((((d.tau : ↥S) : G)) ^ 2) * (((d.rho : ↥S) : G))⁻¹ =
      ((((d.tau : ↥S) : G)) ^ 2)⁻¹ := by
    have h1 : ((d.rho : ↥S) : G) * ((((d.tau : ↥S) : G)) ^ 2) * (((d.rho : ↥S) : G))⁻¹ =
        (((d.rho : ↥S) : G) * (((d.tau : ↥S) : G)) * (((d.rho : ↥S) : G))⁻¹) ^ 2 := by
      rw [← MulAut.conj_apply ((d.rho : ↥S) : G) ((((d.tau : ↥S) : G)) ^ 2),
        map_pow (MulAut.conj ((d.rho : ↥S) : G)) (((d.tau : ↥S) : G)) 2,
        MulAut.conj_apply]
    rw [h1, hconj, inv_pow]
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← hk, ← conj_zpow (a := ((d.rho : ↥S) : G)) (b := (((d.tau : ↥S) : G)) ^ 2) (i := k),
    hconj2]
  have hmem : ((((d.tau : ↥S) : G)) ^ 2) ^ (-k) ∈
      Subgroup.zpowers ((((d.tau : ↥S) : G)) ^ 2) := Subgroup.zpow_mem_zpowers _ _
  simpa [inv_zpow] using hmem

/-- `S` normalizes `⟨τ ^ 2⟩`, i.e. `S ≤ N_G(⟨τ ^ 2⟩)`. -/
lemma sylow_le_normalizer (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    (S : Subgroup G) ≤ Subgroup.normalizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) := by
  have hS : (S : Subgroup G) =
      Subgroup.closure ({((d.tau : ↥S) : G), ((d.rho : ↥S) : G)} : Set G) := by
    have hmap : Subgroup.map (S : Subgroup G).subtype (⊤ : Subgroup ↥S) = (S : Subgroup G) := by
      simpa using (Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) (S : Subgroup G))
    rw [← hmap, ← d.closure_eq_top, MonoidHom.map_closure]
    rw [Set.image_pair]
    simp
  rw [hS, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.centralizer_le_normalizer _ (tau_mem_centralizer S d)
  · exact rho_mem_normalizer S d

/-- `S ∩ C_G(σ) = ⟨τ⟩` where `σ = τ ^ 2`. -/
lemma sylow_inf_centralizer_eq (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) :
    (S : Subgroup G) ⊓ (Subgroup.centralizer
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)) =
      Subgroup.zpowers (((d.tau : ↥S) : G)) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxS, hxC⟩ := hx
    by_contra hxnot
    have hxnot' : (⟨x, hxS⟩ : ↥S) ∉ Subgroup.zpowers d.tau := by
      intro h
      apply hxnot
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      have := congrArg (Subtype.val) hk
      simpa using this
    have hbasic := (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).2.2.2.2
      (⟨x, hxS⟩ : ↥S) hxnot'
    have hconj : x * (((d.tau : ↥S) : G)) * x⁻¹ = (((d.tau : ↥S) : G))⁻¹ := by
      have := congrArg (Subtype.val) hbasic.2
      simpa using this
    have hcen : x * ((((d.tau : ↥S) : G)) ^ 2) * x⁻¹ = (((d.tau : ↥S) : G)) ^ 2 := by
      have h2 := (Subgroup.mem_centralizer_iff.mp hxC) ((((d.tau : ↥S) : G)) ^ 2)
        (Subgroup.mem_zpowers _)
      rw [h2.symm]
      group
    have h3 : x * ((((d.tau : ↥S) : G)) ^ 2) * x⁻¹ = ((((d.tau : ↥S) : G)) ^ 2)⁻¹ := by
      have h1 : x * ((((d.tau : ↥S) : G)) ^ 2) * x⁻¹ =
          (x * (((d.tau : ↥S) : G)) * x⁻¹) ^ 2 := by
        rw [← MulAut.conj_apply x ((((d.tau : ↥S) : G)) ^ 2),
          map_pow (MulAut.conj x) (((d.tau : ↥S) : G)) 2, MulAut.conj_apply]
      rw [h1, hconj, inv_pow]
    have h4 : (((d.tau : ↥S) : G)) ^ 4 = 1 := by
      have h2 : ((((d.tau : ↥S) : G)) ^ 2) = ((((d.tau : ↥S) : G)) ^ 2)⁻¹ := hcen.symm.trans h3
      have h5 : ((((d.tau : ↥S) : G)) ^ 2) * ((((d.tau : ↥S) : G)) ^ 2) = 1 := by
        have h6 : ((((d.tau : ↥S) : G)) ^ 2) * ((((d.tau : ↥S) : G)) ^ 2)⁻¹ = 1 :=
          mul_inv_cancel _
        rwa [← h2] at h6
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
      exact h5
    exact tau_pow_four_ne_one S d hn h4
  · intro x hx
    rw [Subgroup.mem_inf]
    have hxτ : x ∈ Subgroup.zpowers (((d.tau : ↥S) : G)) := hx
    constructor
    · exact Subgroup.zpowers_le.mpr d.tau.2 hxτ
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxτ
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
        (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers (((d.tau : ↥S) : G)) 2) hh)
      rw [← hi, ← hj, ← zpow_add, ← zpow_add]
      congr 1
      ring

/-- A cyclic subgroup (as a subgroup of itself) is cyclic. -/
lemma isCyclic_zpowers_subtype (g : G) : IsCyclic ↥(Subgroup.zpowers g) := by
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨⟨g, Subgroup.mem_zpowers g⟩, ?_⟩
  ext x
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

/-- `ρ ∉ C_G(σ)`. -/
lemma rho_notMem_centralizer (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) :
    ((d.rho : ↥S) : G) ∉ Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) := by
  intro h
  rw [Subgroup.mem_centralizer_iff] at h
  have hcomm := h ((((d.tau : ↥S) : G)) ^ 2) (Subgroup.mem_zpowers _)
  have hconj : ((d.rho : ↥S) : G) * (((d.tau : ↥S) : G)) * (((d.rho : ↥S) : G))⁻¹ =
      (((d.tau : ↥S) : G))⁻¹ := by
    have := congrArg (Subtype.val) d.rho_conj
    simpa using this
  have hρ : ((d.rho : ↥S) : G) * ((((d.tau : ↥S) : G)) ^ 2) * (((d.rho : ↥S) : G))⁻¹ =
      ((((d.tau : ↥S) : G)) ^ 2)⁻¹ := by
    have h1 : ((d.rho : ↥S) : G) * ((((d.tau : ↥S) : G)) ^ 2) * (((d.rho : ↥S) : G))⁻¹ =
        (((d.rho : ↥S) : G) * (((d.tau : ↥S) : G)) * (((d.rho : ↥S) : G))⁻¹) ^ 2 := by
      rw [← MulAut.conj_apply ((d.rho : ↥S) : G) ((((d.tau : ↥S) : G)) ^ 2),
        map_pow (MulAut.conj ((d.rho : ↥S) : G)) (((d.tau : ↥S) : G)) 2,
        MulAut.conj_apply]
    rw [h1, hconj, inv_pow]
  have hρ' : ((d.rho : ↥S) : G) * ((((d.tau : ↥S) : G)) ^ 2) * (((d.rho : ↥S) : G))⁻¹ =
      (((d.tau : ↥S) : G)) ^ 2 := by
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : ((((d.tau : ↥S) : G)) ^ 2) = ((((d.tau : ↥S) : G)) ^ 2)⁻¹ := by
    rw [← hρ, hρ']
  have h5 : ((((d.tau : ↥S) : G)) ^ 2) * ((((d.tau : ↥S) : G)) ^ 2) = 1 := by
    have h6 : ((((d.tau : ↥S) : G)) ^ 2) * ((((d.tau : ↥S) : G)) ^ 2)⁻¹ = 1 :=
      mul_inv_cancel _
    rwa [← h2] at h6
  have h4 : (((d.tau : ↥S) : G)) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
    exact h5
  exact tau_pow_four_ne_one S d hn h4

/-- `N_G(⟨σ⟩)` normalizes `C_G(σ)`. -/
lemma conj_mem_centralizer_of_mem_normalizer (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {n : G}
    (hn : n ∈ Subgroup.normalizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro h hh
  have hh' : n⁻¹ * h * n ∈ Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) := by
    have htmp := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) h).mp hh
    simpa using htmp
  have hcomm := hc (n⁻¹ * h * n) hh'
  calc h * (n * c * n⁻¹) = n * (n⁻¹ * h * n * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * h * n)) * n⁻¹ := by rw [hcomm]
    _ = (n * c * n⁻¹) * h := by group

/-- `N_G(⟨σ⟩) ≤ N_G(C_G(σ))`. -/
lemma normalizer_le_normalizer_centralizer (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    Subgroup.normalizer ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact conj_mem_centralizer_of_mem_normalizer S d hn hc
  · intro hc
    have h := conj_mem_centralizer_of_mem_normalizer S d (Subgroup.inv_mem _ hn) hc
    rwa [show n⁻¹ * (n * c * n⁻¹) * (n⁻¹)⁻¹ = c from by group] at h

/-- `[S : ⟨τ⟩] = 2`. -/
lemma relIndex_zpowers_sylow (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    (Subgroup.zpowers (((d.tau : ↥S) : G))).relIndex (S : Subgroup G) = 2 := by
  have hle : Subgroup.zpowers (((d.tau : ↥S) : G)) ≤ (S : Subgroup G) :=
    Subgroup.zpowers_le.mpr d.tau.2
  have hcard1 : Nat.card ↥((Subgroup.zpowers (((d.tau : ↥S) : G))).subgroupOf (S : Subgroup G)) =
      Nat.card ↥(Subgroup.zpowers (((d.tau : ↥S) : G))) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hcardS : Nat.card ↥(S : Subgroup G) = 2 ^ (d.n + 1) :=
    (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).1
  have hTvcard : Nat.card ↥(Subgroup.zpowers (((d.tau : ↥S) : G))) = 2 ^ d.n := by
    rw [Nat.card_zpowers, orderOf_tau_coe]
  rw [Subgroup.relIndex, Subgroup.index_eq_card_div, hcard1, hTvcard, hcardS, pow_succ,
    mul_comm (2 ^ d.n) 2]
  exact Nat.mul_div_cancel _ (by positivity)

/-- `[N_G(⟨σ⟩) : C_G(σ)]` divides `2 ^ (n - 2)`. -/
lemma index_centralizer_dvd (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    (Subgroup.centralizer
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)) ∣
      2 ^ (d.n - 2) := by
  have h := Work.BrauerSuzuki.Sylow.card_normalizerQuotientCentralizer_dvd_card_mulAut
    (Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2))
  haveI : IsCyclic ↥(Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2)) :=
    isCyclic_zpowers_subtype _
  have hcard : Nat.card (MulAut ↥(Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2))) = 2 ^ (d.n - 2) := by
    rw [IsCyclic.card_mulAut, Nat.card_zpowers, tau_sq_order,
      Work.BrauerSuzuki.Sylow.totient_two_pow]
    rw [show d.n - 1 - 1 = d.n - 2 by omega]
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact h.trans (by rw [hcard])

/-- `[N_G(⟨σ⟩) : C_G(σ)] = 2`. -/
lemma relIndex_centralizer_normalizer (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) :
    (Subgroup.centralizer
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)) = 2 := by
  set C := Subgroup.centralizer
    ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) with hC
  set N := Subgroup.normalizer
    ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) with hN
  set Tv := Subgroup.zpowers (((d.tau : ↥S) : G)) with hTv
  have hSN : (S : Subgroup G) ≤ N := sylow_le_normalizer S d
  have hTvS : Tv ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr d.tau.2
  have hSC : (S : Subgroup G) ⊓ C = Tv := sylow_inf_centralizer_eq S d hn
  have hpow : C.relIndex N ∣ 2 ^ (d.n - 2) := index_centralizer_dvd S d
  have h1 : C.relIndex N ∣ Tv.relIndex N := by
    rw [← hSC]
    exact Subgroup.relIndex_dvd_of_le_left (H := (S : Subgroup G) ⊓ C) (K := C) (L := N) inf_le_right
  have h2 : Tv.relIndex N = Tv.relIndex (S : Subgroup G) * (S : Subgroup G).relIndex N :=
    (Subgroup.relIndex_mul_relIndex (H := Tv) (K := (S : Subgroup G)) (L := N) hTvS hSN).symm
  have h3 : Tv.relIndex (S : Subgroup G) = 2 := relIndex_zpowers_sylow S d
  have hmain : C.relIndex N ∣ 2 * (S : Subgroup G).relIndex N := by
    have h4 : Tv.relIndex N = 2 * (S : Subgroup G).relIndex N := by rw [h2, h3]
    rw [← h4]
    exact h1
  have hodd : Odd ((S : Subgroup G).relIndex N) := by
    have hindex_odd : Odd ((S : Subgroup G).index) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact S.not_dvd_index
    exact Odd.of_dvd_nat hindex_odd (Subgroup.relIndex_dvd_index_of_le hSN)
  obtain ⟨k, hk⟩ : ∃ k, C.relIndex N = 2 ^ k := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpow
    exact ⟨k, hk⟩
  have hdvd2 : C.relIndex N ∣ 2 := by
    rw [hk] at hmain ⊢
    exact (((Nat.coprime_two_right.mpr hodd).pow_right k).symm).dvd_of_dvd_mul_right hmain
  have hne1 : C.relIndex N ≠ 1 := by
    intro h
    have htop : C.subgroupOf N = ⊤ := Subgroup.index_eq_one.mp h
    have hle : N ≤ C := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥N) ∈ C.subgroupOf N := by rw [htop]; trivial
      simpa only [Subgroup.mem_subgroupOf] using hx'
    exact rho_notMem_centralizer S d hn (hle (rho_mem_normalizer S d))
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exact absurd (by rw [hk, h0, pow_zero]) hne1
    · exact hpos
  have h2le : 2 ≤ C.relIndex N := by
    rw [hk]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  exact le_antisymm (Nat.le_of_dvd (by norm_num) hdvd2) h2le

/-- `[N_G(⟨σ⟩) : S]` is odd. -/
lemma odd_relIndex_sylow_normalizer (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    Odd ((S : Subgroup G).relIndex (Subgroup.normalizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G))) := by
  have hSN := sylow_le_normalizer S d
  have hindex_odd : Odd ((S : Subgroup G).index) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact S.not_dvd_index
  exact Odd.of_dvd_nat hindex_odd (Subgroup.relIndex_dvd_index_of_le hSN)

/-- `|C_G(τ ^ 2)| = 2 ^ n * [N_G(⟨τ ^ 2⟩) : S]`. -/
lemma card_centralizer_eq (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) :
    Nat.card ↥(Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)) =
      2 ^ d.n * ((S : Subgroup G).relIndex (Subgroup.normalizer
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G))) := by
  set C := Subgroup.centralizer
    ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) with hC
  set N := Subgroup.normalizer
    ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) with hN
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hSN : (S : Subgroup G) ≤ N := sylow_le_normalizer S d
  have hCrelIndex : (C.subgroupOf N).index = 2 := relIndex_centralizer_normalizer S d hn
  have hcardN1 : Nat.card ↥N = Nat.card ↥C * 2 := by
    have h := Subgroup.card_mul_index (C.subgroupOf N)
    have h2 : Nat.card ↥(C.subgroupOf N) = Nat.card ↥C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
    rw [h2, hCrelIndex] at h
    exact h.symm
  have hcardN2 : Nat.card ↥N = Nat.card ↥(S : Subgroup G) * (S : Subgroup G).relIndex N := by
    have h := Subgroup.card_mul_index ((S : Subgroup G).subgroupOf N)
    have h2 : Nat.card ↥((S : Subgroup G).subgroupOf N) = Nat.card ↥(S : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
    rw [h2] at h
    exact h.symm
  have hScard : Nat.card ↥(S : Subgroup G) = 2 ^ (d.n + 1) :=
    (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).1
  have h : Nat.card ↥C * 2 = 2 ^ d.n * (S : Subgroup G).relIndex N * 2 := by
    rw [← hcardN1, hcardN2, hScard]
    ring
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) h

/-- The exponent of `2` in `|C_G(τ ^ 2)|` is `n`. -/
lemma factorization_card_centralizer (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) :
    (Nat.card ↥(Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G))).factorization 2 = d.n := by
  set N := Subgroup.normalizer
    ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) with hN
  have hodd : Odd ((S : Subgroup G).relIndex N) := odd_relIndex_sylow_normalizer S d
  have ho_ne : (S : Subgroup G).relIndex N ≠ 0 :=
    Subgroup.index_ne_zero_of_finite (H := (S : Subgroup G).subgroupOf N)
  have h2o : ¬ 2 ∣ (S : Subgroup G).relIndex N := by
    rw [← even_iff_two_dvd]
    exact (Nat.not_even_iff_odd).mpr hodd
  rw [card_centralizer_eq S d hn,
    Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) ho_ne]
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd h2o, add_zero]

/-- `C_G(τ ^ 2)` has a cyclic Sylow `2`-subgroup. -/
lemma exists_cyclic_sylow_centralizer (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) :
    ∃ P : Sylow 2 ↥(Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)), IsCyclic ↥P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer
    ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) with hC
  have hτC : Subgroup.zpowers (((d.tau : ↥S) : G)) ≤ C :=
    Subgroup.zpowers_le.mpr (tau_mem_centralizer S d)
  refine ⟨Sylow.ofCard ((Subgroup.zpowers (((d.tau : ↥S) : G))).subgroupOf C) ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hτC).toEquiv, Nat.card_zpowers,
      orderOf_tau_coe]
    congr 1
    exact (factorization_card_centralizer S d hn).symm
  · exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hτC)).mpr
      (isCyclic_zpowers_subtype (((d.tau : ↥S) : G)))

/-- An odd divisor of a power of two is `1`. -/
lemma eq_one_of_dvd_two_pow_of_odd {a k : ℕ} (hdiv : a ∣ 2 ^ k) (hodd : Odd a) : a = 1 := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [hm, h0, pow_zero]
  · exact absurd (hm ▸ hodd) (by
      rw [Nat.not_odd_iff_even, even_iff_two_dvd]
      exact ⟨2 ^ (m - 1), by rw [← pow_succ']; congr 1; omega⟩)

/-- **Dade's Lemma 6.9**: the normal `2`-complement of `C_G(τ ^ 2)`. -/
lemma exists_normal_complement_centralizer (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) :
    ∃ K : Subgroup G,
      K ≤ Subgroup.centralizer
          ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) ∧
      Subgroup.normalizer
          ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (K : Set G) ∧
      Odd (Nat.card K) ∧
      (∀ x ∈ K, x * (((d.tau : ↥S) : G) ^ 2) = (((d.tau : ↥S) : G) ^ 2) * x) ∧
      K ⊓ (S : Subgroup G) = ⊥ ∧
      K ⊔ (S : Subgroup G) = Subgroup.normalizer
          ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) ∧
      K ⊔ Subgroup.zpowers (((d.tau : ↥S) : G)) = Subgroup.centralizer
          ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ : G := ((d.tau : ↥S) : G) with hτ
  set σ : G := τ ^ 2 with hσ
  set Tv : Subgroup G := Subgroup.zpowers τ with hTv
  set C : Subgroup G := Subgroup.centralizer ((Subgroup.zpowers σ : Subgroup G) : Set G) with hC
  set N : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup G) : Set G) with hN
  have hτC : Tv ≤ C := Subgroup.zpowers_le.mpr (tau_mem_centralizer S d)
  have hTvS : Tv ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr d.tau.2
  have hScard : Nat.card ↥(S : Subgroup G) = 2 ^ (d.n + 1) :=
    (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).1
  have hHcard : Nat.card ↥(Tv.subgroupOf C) = 2 ^ (Nat.card ↥C).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hτC).toEquiv, Nat.card_zpowers, hτ,
      orderOf_tau_coe]
    congr 1
    exact (factorization_card_centralizer S d hn).symm
  let P : Sylow 2 ↥C := Sylow.ofCard (Tv.subgroupOf C) hHcard
  have hPcoeeq : (P : Subgroup ↥C) = Tv.subgroupOf C := Sylow.coe_ofCard _ _
  have hPcyc : IsCyclic ↥P :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hτC)).mpr (isCyclic_zpowers_subtype τ)
  obtain ⟨K', hK'⟩ := Work.NPC.frobenius_npc (p := 2)
    (Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow P hPcyc)
  haveI : K'.Normal := hK'.normal
  have hK'odd : Odd (Nat.card ↥K') := Nat.coprime_two_right.mp hK'.coprime_card
  have hK'quot : IsPGroup 2 (↥C ⧸ K') := hK'.isPGroup_quotient
  have hK'card : Nat.card ↥(K'.map C.subtype) = Nat.card ↥K' :=
    Subgroup.card_map_of_injective Subtype.coe_injective
  have hKleC : K'.map C.subtype ≤ C := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hmemK : ∀ x : G, x ∈ C → (x ∈ K'.map C.subtype ↔ Odd (orderOf x)) := by
    intro x hxC
    constructor
    · intro hx
      obtain ⟨y', hy', hy'x⟩ := Subgroup.mem_map.mp hx
      have h2 : orderOf (C.subtype y') = orderOf y' := Subgroup.orderOf_coe y'
      rw [hy'x] at h2
      rw [h2]
      have h4 : orderOf y' = orderOf (⟨y', hy'⟩ : ↥K') :=
        Subgroup.orderOf_coe (⟨y', hy'⟩ : ↥K')
      have h5 : orderOf (⟨y', hy'⟩ : ↥K') ∣ Nat.card ↥K' :=
        orderOf_dvd_natCard (⟨y', hy'⟩ : ↥K')
      exact Odd.of_dvd_nat hK'odd (h4 ▸ h5)
    · intro hodd
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      have hgoal : orderOf ((QuotientGroup.mk' K') ⟨x, hxC⟩) = 1 := by
        obtain ⟨j, hj⟩ := hK'quot.exists_card_eq
        have hdiv1 : orderOf ((QuotientGroup.mk' K') ⟨x, hxC⟩) ∣ 2 ^ j := by
          rw [← hj]
          exact orderOf_dvd_natCard _
        have hdiv2 : orderOf ((QuotientGroup.mk' K') ⟨x, hxC⟩) ∣ orderOf x := by
          have h1 : orderOf ((QuotientGroup.mk' K') ⟨x, hxC⟩) ∣ orderOf (⟨x, hxC⟩ : ↥C) :=
            orderOf_map_dvd _ _
          have h2 : orderOf (⟨x, hxC⟩ : ↥C) = orderOf x := (Subgroup.orderOf_coe _).symm
          rwa [h2] at h1
        exact eq_one_of_dvd_two_pow_of_odd hdiv1 (Odd.of_dvd_nat hodd hdiv2)
      have hker : (QuotientGroup.mk' K') ⟨x, hxC⟩ = 1 := orderOf_eq_one_iff.mp hgoal
      have hmem : ⟨x, hxC⟩ ∈ (QuotientGroup.mk' K').ker := MonoidHom.mem_ker.mpr hker
      rwa [QuotientGroup.ker_mk'] at hmem
  have hNCN : N ≤ Subgroup.normalizer (C : Set G) := normalizer_le_normalizer_centralizer S d
  have hSN : (S : Subgroup G) ≤ N := sylow_le_normalizer S d
  have hSC : (S : Subgroup G) ⊓ C = Tv := by
    rw [hTv, hC, hσ, hτ]
    exact sylow_inf_centralizer_eq S d hn
  have hCSN : C ⊔ (S : Subgroup G) = N := by
    have hleCS : C ⊔ (S : Subgroup G) ≤ N :=
      sup_le (Subgroup.centralizer_le_normalizer _) hSN
    have hSCleC : (S : Subgroup G) ≤ Subgroup.normalizer (C : Set G) :=
      fun x hx => hNCN (hSN hx)
    have hcardinf : Nat.card ↥(C ⊓ (S : Subgroup G)) = 2 ^ d.n := by
      rw [inf_comm, hSC, hTv, Nat.card_zpowers, hτ, orderOf_tau_coe]
    have hCcard : Nat.card ↥C = 2 ^ d.n * (S : Subgroup G).relIndex N :=
      card_centralizer_eq S d hn
    have hNcard : Nat.card ↥N = 2 ^ (d.n + 1) * (S : Subgroup G).relIndex N := by
      have h := Subgroup.card_mul_index ((S : Subgroup G).subgroupOf N)
      have h2 : Nat.card ↥((S : Subgroup G).subgroupOf N) = Nat.card ↥(S : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
      rw [h2, hScard] at h
      exact h.symm
    have hprod := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
      (H := C) (K := (S : Subgroup G)) hSCleC
    rw [hcardinf, hCcard, hScard] at hprod
    have hsup : Nat.card ↥(C ⊔ (S : Subgroup G)) =
        2 ^ (d.n + 1) * (S : Subgroup G).relIndex N := by
      refine Nat.mul_right_cancel (by positivity : 0 < 2 ^ d.n) ?_
      rw [hprod]
      ring
    exact Subgroup.eq_of_le_of_card_ge hleCS (by rw [hsup, hNcard])
  have hK'P : K' ⊔ (P : Subgroup ↥C) = ⊤ :=
    (Work.NPC.Basic.isNormalPComplement_complement_sylow hK' P).sup_eq_top
  have hKtv : K'.map C.subtype ⊔ Tv = C := by
    have hmap := congrArg (Subgroup.map C.subtype) hK'P
    rw [Subgroup.map_sup] at hmap
    rw [hPcoeeq] at hmap
    have htop : (⊤ : Subgroup ↥C).map C.subtype = C := by
      have := Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) (C : Subgroup G)
      simpa using this
    rw [htop] at hmap
    rw [Subgroup.subgroupOf_map_subtype] at hmap
    rwa [inf_eq_left.mpr hτC] at hmap
  refine ⟨K'.map C.subtype, hKleC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have hfwd : ∀ y ∈ K'.map C.subtype, n * y * n⁻¹ ∈ K'.map C.subtype := by
      intro y hy
      have hyC : y ∈ C := hKleC hy
      have hnyC : n * y * n⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hNCN hn) y).mp hyC
      rw [hmemK _ hnyC]
      have hord : orderOf (n * y * n⁻¹) = orderOf y := by
        rw [← MulAut.conj_apply n y, MulEquiv.orderOf_eq]
      rw [hord]
      exact (hmemK y hyC).mp hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hfwd x
    · intro hx
      have h1 : n * x * n⁻¹ ∈ C := hKleC hx
      have hxC : x ∈ C := (Subgroup.mem_normalizer_iff.mp (hNCN hn) x).mpr h1
      rw [hmemK x hxC]
      have hodd : Odd (orderOf (n * x * n⁻¹)) := (hmemK _ h1).mp hx
      have hord : orderOf (n * x * n⁻¹) = orderOf x := by
        rw [← MulAut.conj_apply n x, MulEquiv.orderOf_eq]
      rwa [← hord]
  · rw [hK'card]; exact hK'odd
  · intro x hx
    have hxC : x ∈ C := hKleC hx
    rw [hC, hσ] at hxC
    exact (Subgroup.mem_centralizer_iff.mp hxC (τ ^ 2) (Subgroup.mem_zpowers _)).symm
  · have hKodd : Odd (Nat.card ↥(K'.map C.subtype)) := by rw [hK'card]; exact hK'odd
    have hdivK : Nat.card ↥(K'.map C.subtype ⊓ (S : Subgroup G)) ∣
        Nat.card ↥(K'.map C.subtype) := by
      have h := Subgroup.card_mul_index
        ((K'.map C.subtype ⊓ (S : Subgroup G)).subgroupOf (K'.map C.subtype))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
      exact ⟨_, h.symm⟩
    have hdivS : Nat.card ↥(K'.map C.subtype ⊓ (S : Subgroup G)) ∣
        Nat.card ↥(S : Subgroup G) := by
      have h := Subgroup.card_mul_index
        ((K'.map C.subtype ⊓ (S : Subgroup G)).subgroupOf (S : Subgroup G))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h
      exact ⟨_, h.symm⟩
    have h1 : Nat.card ↥(K'.map C.subtype ⊓ (S : Subgroup G)) = 1 :=
      eq_one_of_dvd_two_pow_of_odd (by rw [hScard] at hdivS; exact hdivS)
        (Odd.of_dvd_nat hKodd hdivK)
    haveI : Subsingleton ↥(K'.map C.subtype ⊓ (S : Subgroup G)) :=
      (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subgroup.eq_bot_of_subsingleton _
  · rw [← hCSN]
    refine le_antisymm ?_ ?_
    · exact sup_le (le_trans hKleC le_sup_left) le_sup_right
    · refine sup_le ?_ le_sup_right
      exact (le_of_eq hKtv.symm).trans (sup_le le_sup_left (le_trans hTvS le_sup_right))
  · exact hKtv

/-- A cyclic subgroup (as a subgroup of itself) is cyclic. -/
lemma mem_zpowers_iff_exists_nat {G : Type*} [Group G] [Finite G] {g h : G} :
    h ∈ Subgroup.zpowers g ↔ ∃ k : ℕ, g ^ k = h := by
  have hx : IsOfFinOrder g := isOfFinOrder_of_finite g
  constructor
  · intro hh
    exact (Submonoid.mem_powers_iff h g).mp (hx.mem_powers_iff_mem_zpowers.mpr hh)
  · rintro ⟨k, hk⟩
    exact hx.mem_powers_iff_mem_zpowers.mp ((Submonoid.mem_powers_iff h g).mpr ⟨k, hk⟩)

/-- `Nat.gcd a (2 ^ n) = 2` when `a` is even but not divisible by `4`. -/
lemma gcd_two_pow_of_two_dvd_of_not_four_dvd {a n : ℕ} (hn : 2 ≤ n) (h2 : 2 ∣ a)
    (h4 : ¬ 4 ∣ a) : Nat.gcd a (2 ^ n) = 2 := by
  have h2' : 2 ∣ Nat.gcd a (2 ^ n) :=
    Nat.dvd_gcd h2 (by simpa using (pow_dvd_pow (2 : ℕ) (show 1 ≤ n by omega) : 2 ^ 1 ∣ 2 ^ n))
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right a (2 ^ n))
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [hj, h0, pow_zero] at h2'
      exact absurd h2' (by norm_num)
    · exact hpos
  have hj2 : j ≤ 1 := by
    by_contra hcon
    have h2j : 2 ≤ j := by omega
    have : 4 ∣ a := by
      refine dvd_trans ?_ (hj ▸ Nat.gcd_dvd_left a (2 ^ n))
      simpa using (pow_dvd_pow (2 : ℕ) h2j : 2 ^ 2 ∣ 2 ^ j)
    exact h4 this
  rw [hj, show j = 1 by omega, pow_one]

/-- The `↥S`-level criterion `τ ^ i ∈ ⟨τ ^ 2⟩ ↔ 2 ∣ i`, transported to `G`. -/
lemma tau_coe_zpow_mem_zpowers_two (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (i : ℤ) :
    (((d.tau : ↥S) : G)) ^ i ∈ Subgroup.zpowers ((((d.tau : ↥S) : G)) ^ 2) ↔ (2 : ℤ) ∣ i := by
  constructor
  · intro h
    rw [Subgroup.mem_zpowers_iff] at h
    obtain ⟨m, hm⟩ := h
    refine ((Work.BrauerSuzuki.Quaternion.tau_zpow_mem_zpowers_two_four d i).1).mp ?_
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    apply Subtype.ext
    simpa using hm
  · intro h
    have h' : (d.tau : ↥S) ^ i ∈ Subgroup.zpowers ((d.tau : ↥S) ^ 2) :=
      ((Work.BrauerSuzuki.Quaternion.tau_zpow_mem_zpowers_two_four d i).1).mpr h
    rw [Subgroup.mem_zpowers_iff] at h' ⊢
    obtain ⟨m, hm⟩ := h'
    exact ⟨m, by simpa using congrArg (Subtype.val) hm⟩

/-- The `↥S`-level criterion `τ ^ i ∈ ⟨τ ^ 4⟩ ↔ 4 ∣ i`, transported to `G`. -/
lemma tau_coe_zpow_mem_zpowers_four (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (i : ℤ) :
    (((d.tau : ↥S) : G)) ^ i ∈ Subgroup.zpowers ((((d.tau : ↥S) : G)) ^ 4) ↔ (4 : ℤ) ∣ i := by
  constructor
  · intro h
    rw [Subgroup.mem_zpowers_iff] at h
    obtain ⟨m, hm⟩ := h
    refine ((Work.BrauerSuzuki.Quaternion.tau_zpow_mem_zpowers_two_four d i).2).mp ?_
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    apply Subtype.ext
    simpa using hm
  · intro h
    have h' : (d.tau : ↥S) ^ i ∈ Subgroup.zpowers ((d.tau : ↥S) ^ 4) :=
      ((Work.BrauerSuzuki.Quaternion.tau_zpow_mem_zpowers_two_four d i).2).mpr h
    rw [Subgroup.mem_zpowers_iff] at h' ⊢
    obtain ⟨m, hm⟩ := h'
    exact ⟨m, by simpa using congrArg (Subtype.val) hm⟩

/-- **Dade's Lemma 6.10**: `√(τ ^ 2) = C_G(τ ^ 2) \ (⟨τ ^ 4⟩ K)`. -/
lemma sqrtSet_eq_sdiff (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G))
    (hKN : Subgroup.normalizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (K : Set G))
    (hKodd : Odd (Nat.card K))
    (hKS : K ⊓ (S : Subgroup G) = ⊥)
    (hKtv : K ⊔ Subgroup.zpowers (((d.tau : ↥S) : G)) = Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)) :
    Work.BrauerSuzuki.sqrtSet (((d.tau : ↥S) : G) ^ 2) =
      ((Subgroup.centralizer
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G)) : Set G) \
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 4) ⊔ K : Subgroup G) : Set G) := by
  set τ : G := ((d.tau : ↥S) : G) with hτ
  set Tv : Subgroup G := Subgroup.zpowers τ with hTv
  set Tv4 : Subgroup G := Subgroup.zpowers (τ ^ 4) with hTv4
  set C : Subgroup G := Subgroup.centralizer ((Subgroup.zpowers (τ ^ 2) : Subgroup G) : Set G)
    with hC
  have hTvS : Tv ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr d.tau.2
  have hTvC : Tv ≤ C := hKtv ▸ le_sup_right
  have hTvN : Tv ≤ Subgroup.normalizer (K : Set G) :=
    fun x hx => hKN (Subgroup.centralizer_le_normalizer _ (hTvC hx))
  have hTv4le : Tv4 ≤ Tv := Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers τ 4)
  have hTv4N : Tv4 ≤ Subgroup.normalizer (K : Set G) := fun x hx => hTvN (hTv4le hx)
  have hKS' : (S : Subgroup G) ⊓ K = ⊥ := by rw [inf_comm]; exact hKS
  have hTvK_bot : Tv ⊓ K = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc Tv ⊓ K ≤ (S : Subgroup G) ⊓ K := inf_le_inf hTvS le_rfl
      _ = ⊥ := hKS'
  have hmemK_odd : ∀ x ∈ K, Odd (orderOf x) := by
    intro x hx
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : K)
    have h2 : orderOf x = orderOf (⟨x, hx⟩ : K) := Subgroup.orderOf_coe (⟨x, hx⟩ : K)
    exact Odd.of_dvd_nat hKodd (h2 ▸ h)
  have hσcomm : ∀ x ∈ C, (τ ^ 2) * x = x * (τ ^ 2) := by
    intro x hx
    rw [hC] at hx
    exact Subgroup.mem_centralizer_iff.mp hx (τ ^ 2) (Subgroup.mem_zpowers _)
  -- `C = ⟨τ⟩ · K` as sets
  have hCprod : (C : Set G) = (Tv : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Tv K hTvN, sup_comm, hKtv]
  have hTv4prod : ((Subgroup.zpowers (τ ^ 4) ⊔ K : Subgroup G) : Set G) =
      (Tv4 : Set G) * (K : Set G) := Subgroup.coe_mul_of_left_le_normalizer_right Tv4 K hTv4N
  -- modulo `K`, powers of `a * k` reduce to powers of `a`
  have hkey : ∀ (a k : G), a ∈ Tv → k ∈ K → ∀ m : ℕ, ∃ k' ∈ K, (a * k) ^ m = a ^ m * k' := by
    intro a k ha hk m
    induction m with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ m ih =>
        obtain ⟨k', hk', hk'eq⟩ := ih
        have hconj : a⁻¹ * k' * a ∈ K := by
          have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTvN ha)) k').mp hk'
          simpa using h
        refine ⟨(a⁻¹ * k' * a) * k, K.mul_mem hconj hk, ?_⟩
        rw [pow_succ, hk'eq, pow_succ]
        group
  -- the even case: `2 ∣ i`, `4 ∤ i`
  have heven : ∀ (a k : G) (i : ℤ), a ∈ Tv → τ ^ i = a → (2 : ℤ) ∣ i → ¬ (4 : ℤ) ∣ i →
      k ∈ K → τ ^ 2 ∈ Subgroup.zpowers (a * k) := by
    intro a k i ha hai h2i h4i hk
    have hkC : k ∈ C := hKC hk
    have haσ : a ∈ Subgroup.zpowers (τ ^ 2) := by
      rw [← hai]
      exact (tau_coe_zpow_mem_zpowers_two S d i).mpr h2i
    have hak : a * k = k * a := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp haσ
      have hc : Commute (τ ^ 2) k := hσcomm k hkC
      have hcomm_j : (τ ^ 2) ^ j * k = k * (τ ^ 2) ^ j := hc.zpow_left j
      rw [← hj]
      exact hcomm_j
    have h2n : 2 ∣ i.natAbs := Int.natCast_dvd.mp h2i
    have h4n : ¬ 4 ∣ i.natAbs := fun h => h4i (Int.natCast_dvd.mpr h)
    have horder_a : orderOf a = 2 ^ (d.n - 1) := by
      rw [← hai, orderOf_zpow, orderOf_tau_coe, Nat.gcd_comm]
      rw [gcd_two_pow_of_two_dvd_of_not_four_dvd (by omega) h2n h4n,
        show 2 ^ d.n = 2 ^ (d.n - 1) * 2 from by rw [← pow_succ]; congr 1; omega]
      exact Nat.mul_div_cancel _ (by norm_num)
    have hcop : (orderOf a).Coprime (orderOf k) := by
      rw [horder_a]
      exact ((Nat.coprime_two_right.mpr (hmemK_odd k hk)).pow_right (d.n - 1)).symm
    have hjoin := zpowers_sup_of_commute_coprime hak hcop
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers (a * k) := by
      rw [← hjoin]
      exact le_sup_left
    have hcard : Nat.card ↥(Subgroup.zpowers (τ ^ 2)) = Nat.card ↥(Subgroup.zpowers a) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, tau_sq_order, horder_a]
    have heq : Subgroup.zpowers a = Subgroup.zpowers (τ ^ 2) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haσ) (le_of_eq hcard)
    exact hle (heq ▸ Subgroup.mem_zpowers (τ ^ 2))
  ext y
  constructor
  · intro hy
    have hyC : y ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro h hh
      have hyy : y * τ ^ 2 = τ ^ 2 * y := by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← hm]
        exact (Commute.refl y).zpow_right m
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute (τ ^ 2) y := hyy.symm
      have hcomm_j : (τ ^ 2) ^ j * y = y * (τ ^ 2) ^ j := hc.zpow_left j
      rw [← hj]
      exact hcomm_j
    refine ⟨hyC, ?_⟩
    intro hmem
    obtain ⟨a, ha, k, hk, hak⟩ :=
      Set.mem_mul.mp (hCprod ▸ (show y ∈ (C : Set G) from hyC))
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    have havt4 : a ∈ Tv4 := by
      obtain ⟨t, ht, k'', hk'', htk''⟩ :=
        Set.mem_mul.mp (hTv4prod ▸ (show y ∈ ((Subgroup.zpowers (τ ^ 4) ⊔ K : Subgroup G) : Set G)
          from hmem))
      have hatK : a * t⁻¹ ∈ K := by
        have h1 : a * k = t * k'' := by rw [hak, ← htk'']
        have heq : a * t⁻¹ = t * (k'' * k⁻¹) * t⁻¹ := by
          calc a * t⁻¹ = (a * k) * k⁻¹ * t⁻¹ := by group
            _ = (t * k'') * k⁻¹ * t⁻¹ := by rw [h1]
            _ = t * (k'' * k⁻¹) * t⁻¹ := by group
        rw [heq]
        exact (Subgroup.mem_normalizer_iff.mp (hTv4N ht) _).mp
          (K.mul_mem hk'' (Subgroup.inv_mem _ hk))
      have h2 : a * t⁻¹ = 1 := by
        have hmem_bot : a * t⁻¹ ∈ Tv ⊓ K :=
          Subgroup.mem_inf.mpr ⟨Tv.mul_mem ha (Subgroup.inv_mem _ (hTv4le ht)), hatK⟩
        rw [hTvK_bot] at hmem_bot
        simpa using hmem_bot
      have haeq : a = t := mul_inv_eq_one.mp h2
      rw [haeq]
      exact ht
    have h4i : (4 : ℤ) ∣ i :=
      (tau_coe_zpow_mem_zpowers_four S d i).mp (by rw [hi]; exact havt4)
    obtain ⟨m, hm⟩ := mem_zpowers_iff_exists_nat.mp hy
    obtain ⟨k', hk', hk'eq⟩ := hkey a k ha hk m
    have hτ2N : τ ^ 2 ∈ Subgroup.normalizer (K : Set G) :=
      hKN (Subgroup.centralizer_le_normalizer _ (C.pow_mem (tau_mem_centralizer S d) 2))
    have hKa : a ^ m * (τ ^ 2)⁻¹ ∈ K := by
      have h1 : τ ^ 2 = a ^ m * k' := by rw [← hm, ← hak, hk'eq]
      have h2 : a ^ m = τ ^ 2 * k'⁻¹ := by
        have h3 : τ ^ 2 * k'⁻¹ = a ^ m := by rw [h1, mul_assoc, mul_inv_cancel, mul_one]
        exact h3.symm
      rw [h2]
      exact (Subgroup.mem_normalizer_iff.mp hτ2N k'⁻¹).mp (Subgroup.inv_mem _ hk')
    have hKa' : τ ^ (i * (m : ℤ) - 2) ∈ K := by
      have h4 : a ^ m = τ ^ (i * (m : ℤ)) := by rw [← hi, ← zpow_natCast, zpow_mul]
      have h5 : a ^ m * (τ ^ 2)⁻¹ = τ ^ (i * (m : ℤ) - 2) := by
        rw [h4, ← zpow_natCast τ 2, ← zpow_sub]
        norm_num
      rwa [h5] at hKa
    have h1 : τ ^ (i * (m : ℤ) - 2) = 1 := by
      have hmem' : τ ^ (i * (m : ℤ) - 2) ∈ Tv ⊓ K :=
        Subgroup.mem_inf.mpr ⟨Subgroup.zpow_mem_zpowers _ _, hKa'⟩
      rw [hTvK_bot] at hmem'
      simpa using hmem'
    have h2 : (2 : ℤ) ^ d.n ∣ i * (m : ℤ) - 2 := by
      have h1' : ((orderOf τ : ℕ) : ℤ) ∣ i * (m : ℤ) - 2 :=
        orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [orderOf_tau_coe] at h1'
      simpa [Nat.cast_pow] using h1'
    have h3 : (4 : ℤ) ∣ i * (m : ℤ) - 2 := by
      refine dvd_trans ?_ h2
      have h4dvd : (4 : ℤ) ∣ (2 : ℤ) ^ d.n := by
        have h := pow_dvd_pow (2 : ℤ) (show 2 ≤ d.n by omega)
        simpa using h
      exact h4dvd
    have h4' : (4 : ℤ) ∣ i * (m : ℤ) := dvd_mul_of_dvd_left h4i _
    have h5 : (4 : ℤ) ∣ 2 := by
      have h6 : (4 : ℤ) ∣ i * (m : ℤ) - (i * (m : ℤ) - 2) := dvd_sub h4' h3
      convert h6 using 1
      ring
    norm_num at h5
  · rintro ⟨hyC, hynot⟩
    rw [Work.BrauerSuzuki.mem_sqrtSet]
    obtain ⟨a, ha, k, hk, hak⟩ :=
      Set.mem_mul.mp (hCprod ▸ (show y ∈ (C : Set G) from hyC))
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h4i : ¬ (4 : ℤ) ∣ i := by
      intro h4
      have havt4 : a ∈ Tv4 := by
        rw [← hi]
        exact (tau_coe_zpow_mem_zpowers_four S d i).mpr h4
      have : y ∈ ((Subgroup.zpowers (τ ^ 4) ⊔ K : Subgroup G) : Set G) :=
        hTv4prod.symm ▸ Set.mem_mul.mpr ⟨a, havt4, k, hk, hak⟩
      exact hynot this
    by_cases h2i : (2 : ℤ) ∣ i
    · rw [← hak]
      exact heven a k i ha hi h2i h4i hk
    · have h2' : (2 : ℤ) ∣ 2 * i := dvd_mul_right 2 i
      have h4' : ¬ (4 : ℤ) ∣ 2 * i := by
        intro h
        obtain ⟨j, hj⟩ := h
        apply h2i
        refine ⟨j, ?_⟩
        have hh : 2 * i = 2 * (2 * j) := by rw [hj]; ring
        exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hh
      have ha2 : a ^ 2 ∈ Tv := Tv.pow_mem ha 2
      have hτi : τ ^ (2 * i) = a ^ 2 := by
        rw [← hi, ← zpow_natCast, ← zpow_mul]
        congr 1
        ring
      have hkK : a⁻¹ * k * a * k ∈ K := by
        have h1 : a⁻¹ * k * a ∈ K := by
          have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTvN ha)) k).mp hk
          simpa using h
        exact K.mul_mem h1 hk
      have hz : a ^ 2 * (a⁻¹ * k * a * k) = (a * k) * (a * k) := by group
      have hznot : (a * k) * (a * k) ∉ (Subgroup.zpowers (τ ^ 4) ⊔ K : Subgroup G) := by
        intro hmem
        obtain ⟨t, ht, k'', hk'', htk''⟩ :=
          Set.mem_mul.mp (hTv4prod ▸ (show (a * k) * (a * k) ∈
            ((Subgroup.zpowers (τ ^ 4) ⊔ K : Subgroup G) : Set G) from hmem))
        have h2K : a ^ 2 * t⁻¹ ∈ K := by
          have heq : a ^ 2 * t⁻¹ = t * (k'' * (a⁻¹ * k * a * k)⁻¹) * t⁻¹ := by
            calc a ^ 2 * t⁻¹
                = (a ^ 2 * (a⁻¹ * k * a * k)) * (a⁻¹ * k * a * k)⁻¹ * t⁻¹ := by group
              _ = ((a * k) * (a * k)) * (a⁻¹ * k * a * k)⁻¹ * t⁻¹ := by rw [hz]
              _ = (t * k'') * (a⁻¹ * k * a * k)⁻¹ * t⁻¹ := by rw [← htk'']
              _ = t * (k'' * (a⁻¹ * k * a * k)⁻¹) * t⁻¹ := by group
          rw [heq]
          exact (Subgroup.mem_normalizer_iff.mp (hTv4N ht) _).mp
            (K.mul_mem hk'' (Subgroup.inv_mem _ hkK))
        have h2Tv : a ^ 2 * t⁻¹ ∈ Tv := Tv.mul_mem ha2 (Subgroup.inv_mem _ (hTv4le ht))
        have h2bot : a ^ 2 * t⁻¹ ∈ Tv ⊓ K := Subgroup.mem_inf.mpr ⟨h2Tv, h2K⟩
        rw [hTvK_bot] at h2bot
        have h2one : a ^ 2 * t⁻¹ = 1 := by simpa using h2bot
        have h2eq : a ^ 2 = t := mul_inv_eq_one.mp h2one
        have : τ ^ (2 * i) ∈ Tv4 := by
          rw [hτi, h2eq]
          exact ht
        exact h4' ((tau_coe_zpow_mem_zpowers_four S d (2 * i)).mp this)
      have hres : τ ^ 2 ∈ Subgroup.zpowers ((a * k) * (a * k)) := by
        have h1 := heven (a ^ 2) (a⁻¹ * k * a * k) (2 * i) ha2 hτi h2' h4' hkK
        rwa [hz] at h1
      rw [← hak]
      have hmem : (a * k) * (a * k) ∈ Subgroup.zpowers (a * k) := by
        rw [← pow_two]
        exact Subgroup.npow_mem_zpowers (a * k) 2
      exact Subgroup.zpowers_le.mpr hmem hres

/-- **Dade's Lemmas 6.9 and 6.10** (corrected statement). -/
theorem complement_and_sqrtSet {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) :
    ∃ K : Subgroup G,
      K ≤ Subgroup.normalizer (Subgroup.zpowers ((d.tau : G) ^ 2)) ∧
      Subgroup.normalizer (Subgroup.zpowers ((d.tau : G) ^ 2)) ≤ Subgroup.normalizer (K : Set G) ∧
      K ⊓ (S : Subgroup G) = ⊥ ∧
      K ⊔ (S : Subgroup G) = Subgroup.normalizer (Subgroup.zpowers ((d.tau : G) ^ 2)) ∧
      Odd (Nat.card K) ∧ (∀ x ∈ K, x * ((d.tau : G) ^ 2) = ((d.tau : G) ^ 2) * x) ∧
      Work.BrauerSuzuki.sqrtSet ((d.tau : G) ^ 2) =
        ((Subgroup.zpowers (d.tau : G) : Set G) * (K : Set G)) \
          ((Subgroup.zpowers ((d.tau : G) ^ 4) : Set G) * (K : Set G)) := by
  obtain ⟨K, hKC, hKN, hKodd, hKcent, hKS, hKSup, hKtv⟩ :=
    exists_normal_complement_centralizer S d hn
  refine ⟨K, hKC.trans (Subgroup.centralizer_le_normalizer _), hKN, hKS, hKSup, hKodd,
    hKcent, ?_⟩
  have hTvC : Subgroup.zpowers (((d.tau : ↥S) : G)) ≤ Subgroup.centralizer
      ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 2) : Subgroup G) : Set G) := by
    rw [← hKtv]
    exact le_sup_right
  have hTvN : Subgroup.zpowers (((d.tau : ↥S) : G)) ≤ Subgroup.normalizer (K : Set G) :=
    fun x hx => hKN (Subgroup.centralizer_le_normalizer _ (hTvC hx))
  have hTv4le : Subgroup.zpowers ((((d.tau : ↥S) : G)) ^ 4) ≤
      Subgroup.zpowers (((d.tau : ↥S) : G)) :=
    Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers (((d.tau : ↥S) : G)) 4)
  have hTv4N : Subgroup.zpowers ((((d.tau : ↥S) : G)) ^ 4) ≤
      Subgroup.normalizer (K : Set G) := fun x hx => hTvN (hTv4le hx)
  rw [sqrtSet_eq_sdiff S d hn hKC hKN hKodd hKS hKtv]
  congr 1
  · rw [← Subgroup.coe_mul_of_left_le_normalizer_right
      (Subgroup.zpowers (((d.tau : ↥S) : G))) K hTvN, sup_comm, hKtv]
  · exact Subgroup.coe_mul_of_left_le_normalizer_right
      (Subgroup.zpowers ((((d.tau : ↥S) : G)) ^ 4)) K hTv4N

end Work.BrauerSuzuki.Dade
