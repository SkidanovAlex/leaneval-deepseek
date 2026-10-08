import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.bgData_of_setup
import Submission.Work.CORE3.SylowFromLocalControl
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.Case1aBFpf
import Submission.Work.CORE3.Case1aFrattiniSAct
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.fittingPiIn_eq_iSup_pCoreIn
import Submission.Work.CORE3.c1aDirPcommF3
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.isPGroup_le_or_inf_eq_bot_of_isHallIn
import Submission.Work.CORE3.ncard_invSet_eq_one_of_le_centralizer

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.CORE3

open scoped commutatorElement
open Subgroup
open Work.GW2

/-- In an odd-order subgroup, the only element of order dividing `2` is `1`. -/
theorem c1aEqOneOfMulSelfOdd {G : Type} [Group G] [Finite G] {U : Subgroup G}
    (hU : Odd (Nat.card U)) {y : G} (hy : y ∈ U) (h : y * y = 1) : y = 1 := by
  have hdvd : orderOf y ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hy
  have h2 : orderOf y ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using h
  have hne : orderOf y ≠ 2 := fun hh => by
    rw [hh] at hdvd
    exact (Nat.not_even_iff_odd.mpr hU) (even_iff_two_dvd.mpr hdvd)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd h1 hne

/-- In a cyclic subgroup of order `4`, an element different from `1` and from a given
involution generates it. -/
theorem zpowers_eq_of_isCyclic_card_four {G : Type} [Group G] {S0 : Subgroup G}
    (hcyc : IsCyclic ↥S0) (hcard : Nat.card ↥S0 = 4)
    {t x : G} (ht : t ∈ S0) (ht2 : orderOf t = 2) (hx : x ∈ S0) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    Subgroup.zpowers x = S0 := by
  haveI : IsCyclic ↥S0 := hcyc
  haveI : Finite ↥S0 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd : orderOf x ∣ 4 := by
    rw [← hcard]; exact Subgroup.orderOf_dvd_natCard S0 hx
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have hne3 : orderOf x ≠ 3 := fun h => by rw [h] at hdvd; norm_num at hdvd
  have hne2 : orderOf x ≠ 2 := by
    intro h2
    have hcardx : Nat.card (Subgroup.zpowers (⟨x, hx⟩ : ↥S0)) = 2 := by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, h2]
    have hcardt : Nat.card (Subgroup.zpowers (⟨t, ht⟩ : ↥S0)) = 2 := by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, ht2]
    have heq : Subgroup.zpowers (⟨x, hx⟩ : ↥S0) = Subgroup.zpowers (⟨t, ht⟩ : ↥S0) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, hcardx, hcardt]
    have hmem : (⟨x, hx⟩ : ↥S0) ∈ Subgroup.zpowers (⟨t, ht⟩ : ↥S0) :=
      heq ▸ Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hkt : t ^ k = x := by
      have := congrArg (Subtype.val) hk
      simpa using this
    have ht2z : t ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]; rw [← ht2]
      exact pow_orderOf_eq_one t
    have hmod : t ^ (k % (2 : ℤ)) = x := by rw [← hkt, zpow_eq_zpow_emod k ht2z]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero] at hmod; exact hx1 hmod.symm
    · rw [h, zpow_one] at hmod; exact hxt hmod.symm
  have hle : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 1 ≤ orderOf x := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hxord : orderOf x = 4 := by
    interval_cases orderOf x
    · exact absurd rfl hne1
    · exact absurd rfl hne2
    · exact absurd rfl hne3
    · rfl
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_
  rw [hcard, Nat.card_zpowers, hxord]

/-- The `gen` clause of the `BGData` of `(B.S, B.S0, B.t, D.t1, D.t2)`: `t₁t₂` generates the
cyclic `S₀`.  The proof uses `|S| = 8` (hence `|S₀| = 4`, so `S₀` has a unique involution
`t = B.t`) and `t₁t₂ ∉ {1, t}`, the latter because `t₁t₂` inverts the nontrivial `p`-group
`O_p(U)` while `t` and `t₁` centralize it. -/
theorem Case1aThmCGen (I : Case1Inputs) (hFr : Case1aFrattiniProp) (hA7 : Case1aA7Prop) :
    ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
      Case1 B → B.Hhat = B.H → ∀ D : Case1aData B,
        B.S0 = Subgroup.zpowers (D.t1 * D.t2) := by
  intro G _instG _finG hFT hCtx B hCase1 hHhat D
  classical
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  haveI : IsSimpleGroup G := hCtx.simple
  set Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hBcdef
  have hpB : D.p ∣ Nat.card Bc := by
    by_contra hpdvd
    have hrel : ¬ D.p ∣ (⊥ : Subgroup G).relIndex Bc := by
      rwa [Subgroup.relIndex_bot_left]
    exact (hFr G hFT hCtx B hCase1 hHhat D ⊥ bot_le IsPGroup.of_bot hrel).2.2 rfl
  obtain ⟨P2, hP2le, hP2grp, hP2ndvd⟩ := bfpf_exists_pSubgroup_le_of_dvd D.p Bc hpB
  have hP2Hhat : P2 ≤ B.Hhat :=
    hP2le.trans (le_trans inf_le_left (Work.CORE2A.bSetup_U_le_Hhat B))
  have hNHat_ne : Subgroup.normalizer (P2 : Set G) ≠ ⊤ := by
    intro htop
    haveI : P2.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P2 with h | h
    · exact (hFr G hFT hCtx B hCase1 hHhat D P2 hP2le hP2grp hP2ndvd).2.2 h
    · rw [h] at hP2Hhat
      exact B.Hhat_coatom.ne_top (top_le_iff.mp hP2Hhat)
  obtain ⟨M, hMcoat, hNM⟩ := bfpf_exists_isCoatom_le_of_ne_top _ hNHat_ne
  obtain ⟨_hSM, _hV2E, _hiso, hS8, hP0card⟩ :=
    hA7 G hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  have hcardS0 : Nat.card B.S0 = 4 := by
    have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [B.S0_index, inf_eq_left.mpr B.S0_le, hS8] at h
    omega
  have hPne : pCoreIn D.p B.U ≠ ⊥ := by
    intro h; rw [h, bot_inf_eq] at hP0card; simp at hP0card
  obtain ⟨y, hyP, hyne⟩ : ∃ y, y ∈ pCoreIn D.p B.U ∧ y ≠ 1 := by
    by_contra hcon
    apply hPne
    apply le_antisymm _ bot_le
    intro z hz
    rw [Subgroup.mem_bot]
    by_contra hzne
    exact hcon ⟨z, hz, hzne⟩
  have hx_mem : D.t1 * D.t2 ∈ B.S0 := by
    have hidxK : (B.S0.subgroupOf (B.S : Subgroup G)).index = 2 := B.S0_index
    have haK : (⟨D.t1, D.t1_mem⟩ : ↥(B.S : Subgroup G)) ∉
        B.S0.subgroupOf (B.S : Subgroup G) := by
      rw [Subgroup.mem_subgroupOf]; exact D.t1_nmem
    have hbK : (⟨D.t2, D.t2_mem⟩ : ↥(B.S : Subgroup G)) ∉
        B.S0.subgroupOf (B.S : Subgroup G) := by
      rw [Subgroup.mem_subgroupOf]; exact D.t2_nmem
    have hiff := Subgroup.mul_mem_iff_of_index_two (H := B.S0.subgroupOf (B.S : Subgroup G)) hidxK
      (a := (⟨D.t1, D.t1_mem⟩ : ↥(B.S : Subgroup G)))
      (b := (⟨D.t2, D.t2_mem⟩ : ↥(B.S : Subgroup G)))
    have hm : (⟨D.t1, D.t1_mem⟩ : ↥(B.S : Subgroup G)) * ⟨D.t2, D.t2_mem⟩ ∈
        B.S0.subgroupOf (B.S : Subgroup G) := by
      rw [hiff]; exact ⟨fun h => absurd h haK, fun h => absurd h hbK⟩
    have hm2 := Subgroup.mem_subgroupOf.mp hm
    simpa using hm2
  have hxinv : ∀ z ∈ pCoreIn D.p B.U, (D.t1 * D.t2) * z * (D.t1 * D.t2)⁻¹ = z⁻¹ := by
    intro z hz
    have hc : D.t1 * z = z * D.t1 :=
      (Subgroup.mem_centralizer_iff.mp (D.cent hz)) D.t1 (Set.mem_singleton D.t1)
    have hi := D.inv z hz
    calc (D.t1 * D.t2) * z * (D.t1 * D.t2)⁻¹
        = D.t1 * (D.t2 * z * D.t2⁻¹) * D.t1⁻¹ := by group
      _ = D.t1 * z⁻¹ * D.t1⁻¹ := by rw [hi]
      _ = (D.t1 * z * D.t1⁻¹)⁻¹ := by group
      _ = z⁻¹ := by rw [show D.t1 * z * D.t1⁻¹ = z from by rw [hc]; group]
  have hyU : y ∈ B.U := c1aPcoreIn_le_self D.p B.U hyP
  have hyodd := Work.CORE2A.bSetup_U_odd B
  have hx1 : D.t1 * D.t2 ≠ 1 := by
    intro h1
    have hyC : (D.t1 * D.t2) * y * (D.t1 * D.t2)⁻¹ = y := by rw [h1]; simp
    have hyinv : y = y⁻¹ := hyC.symm.trans (hxinv y hyP)
    have hyy : y * y = 1 := by nth_rewrite 2 [hyinv]; exact mul_inv_cancel y
    exact hyne (c1aEqOneOfMulSelfOdd hyodd hyU hyy)
  have hxt : D.t1 * D.t2 ≠ B.t := by
    intro ht_eq
    have hmem : y ∈ Subgroup.centralizer ({B.t} : Set G) :=
      Work.CORE2A.bSetup_U_le_H B hyU
    have hcy := (Subgroup.mem_centralizer_iff.mp hmem) B.t (Set.mem_singleton B.t)
    have hyC : (D.t1 * D.t2) * y * (D.t1 * D.t2)⁻¹ = y := by
      rw [ht_eq, hcy]; group
    have hyinv : y = y⁻¹ := hyC.symm.trans (hxinv y hyP)
    have hyy : y * y = 1 := by nth_rewrite 2 [hyinv]; exact mul_inv_cancel y
    exact hyne (c1aEqOneOfMulSelfOdd hyodd hyU hyy)
  exact (zpowers_eq_of_isCyclic_card_four B.S0_cyclic hcardS0 B.t_mem B.t_order
    hx_mem hx1 hxt).symm

/-- Bender 1981, §3, p. 222: "As `S` centralizes `U/F(U)`", hence `U = F(U)·C_U(S)`. -/
theorem c1aU_eq_fitting_sup_B (I : Case1Inputs) (G : Type) [Group G] [Finite G]
    (hFT : FeitThompsonProp) (hCtx : BenderCtx G) (B : BenderSetup G) (hCase1 : Case1 B) :
    B.U = fittingIn B.U ⊔ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSact := Case1aFrattiniSAct G hFT I.T hCtx B hCase1
  have hSnorm : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := fun s hs =>
    Work.CORE2A.bender_s_mem_normalizer_U B hs
  have hcop : Nat.Coprime 2 (Nat.card B.U) :=
    Nat.coprime_comm.mpr ((Nat.coprime_two_right).mpr (Work.CORE2A.bSetup_U_odd B))
  have hsplit := (I.T.c11i G 2 (B.S : Subgroup G) B.U B.S.isPGroup' hcop hSnorm).2
  have hcommle : ⁅(B.S : Subgroup G), B.U⁆ ≤ fittingIn B.U := by
    rw [Subgroup.commutator_le]
    intro s hs u hu
    have hz : u⁻¹ * (s * u * s⁻¹) ∈ fittingIn B.U := hSact s hs u hu
    have hconj : (⁅s, u⁆ : G) = u * (u⁻¹ * (s * u * s⁻¹)) * u⁻¹ := by
      rw [commutatorElement_def]; group
    rw [hconj]
    obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hz
    haveI : (Work.GW2.fitting ↥B.U).Normal := Subgroup.normalCore_normal _
    refine Subgroup.mem_map.mpr ⟨⟨u, hu⟩ * m * ⟨u, hu⟩⁻¹, ?_, ?_⟩
    · exact (inferInstance : (Work.GW2.fitting ↥B.U).Normal).conj_mem m hm ⟨u, hu⟩
    · rw [← hmeq]; simp
  have hle1 : fittingIn B.U ⊔ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ≤ B.U :=
    sup_le (c1aFittingIn_le B.U) inf_le_left
  have hle2 : B.U ≤ fittingIn B.U ⊔ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) := by
    have h : ⁅(B.S : Subgroup G), B.U⁆ ⊔ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ≤
        fittingIn B.U ⊔ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) :=
      sup_le (hcommle.trans le_sup_left) le_sup_right
    rwa [hsplit] at h
  exact le_antisymm hle2 hle1

/-- In the §3 setting, `O_3(U)` commutes with `F_{3'}(U)` (both are normal subgroups of the
nilpotent `F(U)` of coprime order). -/
theorem c1aPcommF3 {G : Type} [Group G] [Finite G] (B : BenderSetup G) :
    ⁅pCoreIn 3 B.U, fittingPiIn ({3}ᶜ) B.U⁆ = ⊥ :=
  c1aDirPcommF3 B.U

/-- `F(K) = O_3(K) ⊔ F_{3'}(K)`: the nilpotent splitting of the Fitting subgroup at the prime
`3`. -/
theorem c1aFittingIn_eq_sup_three {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    fittingIn K = fittingPiIn ({3}ᶜ) K ⊔ pCoreIn 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ (sup_le (bfpf_fittingPiIn_le_fittingIn _ _) (c1aPcoreIn_le_fittingIn 3 K))
  rw [c1aFittingIn_eq_iSup_pCoreIn K]
  refine iSup_le fun q => ?_
  by_cases hq : (q : ℕ) = 3
  · rw [hq]; exact le_sup_right
  · refine le_sup_of_le_left ?_
    haveI hq' : Fact (Nat.Prime (q : ℕ)) := ⟨q.2⟩
    have hpi : Subgroup.IsPiSubgroup ({3}ᶜ) (Work.GW2.pCore (q : ℕ) ↥K) :=
      Subgroup.isPiSubgroup_of_isPGroup_of_mem
        (Work.CORE2A.pCore_isPGroup_of_finite (H := ↥K) (p := (q:ℕ)))
        (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hq)
    have h1 : Work.GW2.pCore (q : ℕ) ↥K ≤
        (Work.GW2.piCore ({3}ᶜ) ↥(Work.GW2.fitting ↥K)).map (Work.GW2.fitting ↥K).subtype :=
      Work.DSTR.FittingPiImg.le_map_piCore_of_le_of_normal (M := ↥K) ({3}ᶜ)
        (Work.CORE2A.pCore_le_fitting (G := ↥K) (p := (q:ℕ))) hpi
    exact Subgroup.map_mono (f := K.subtype) h1

end Work.CORE3
