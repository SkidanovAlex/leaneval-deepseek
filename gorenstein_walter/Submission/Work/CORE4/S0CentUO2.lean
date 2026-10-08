/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — `S₀ ≤ C_G(U)` from the single §4 (7) identity `O₂(H ⊓ M) = O₂(H)`

`Work.CORE4.Case2S0_comm_U` (`Case2S0_comm_U.lean`) proves `⁅S₀, U⁆ = ⊥` in the §4
configuration, but takes the whole `Case2SevenFacts` (§4 (7)) as a hypothesis, and uses only its
first conjunct `pCoreIn 2 (H ⊓ M) = pCoreIn 2 H`.  This file isolates that use: the same proof,
with the single identity as the hypothesis.  Together with `Work.CORE4.SevenO2HM` (delegated) it
gives the unconditional `S₀ ≤ C_G(U)`, which is the input of `Work.CORE4.Case2NotInvNormal`
(Bender 1981, §4, p. 227: `S₀ = O₂(H ∩ E) = O₂(H) = C_S(U)`).
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2Parity
import Submission.Work.CORE4.Case2BGData
import Submission.Work.CORE4.Case2PrePlusOfCtx
import Submission.Work.CORE4.S0CentK
import Submission.Work.CORE4.Case2S0_comm_U
import Submission.Work.CORE4.dihedral_odd_cyclic_comm
import Submission.Work.CORE4.SevenO2HM
import Submission.Work.CORE4.Case2NotInvNormal

namespace Work.CORE4

open scoped MatrixGroups
open Subgroup

variable {G : Type} [Group G] [Finite G]


/-! ## Local copies of two `Case2S0_comm_U` helpers

Other areas of CORE4 also define `le_pCoreIn_of_normal_isPGroup` (with a different argument
order), so those names are ambiguous once `Case2NotInvNormal` is imported; these local copies
are used instead. -/

/-- Every normal `p`-subgroup of `X` lies in the `p`-core `O_p(X)`, in the `pCoreIn` form. -/
theorem pcoreOfNormal {p : ℕ} {X P : Subgroup G} (hPX : P ≤ X)
    (hN : (P.subgroupOf X).Normal) (hP : IsPGroup p (P.subgroupOf X)) :
    P ≤ Work.GW2.pCoreIn p X := by
  have h1 : P.subgroupOf X ≤ Work.GW2.pCore p ↥X :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hN, hP⟩)
  rintro x hx
  refine ⟨⟨x, hPX hx⟩, h1 ?_, rfl⟩
  rwa [Subgroup.mem_subgroupOf]

/-- `O_2(X)` is a `2`-group. -/
theorem pcoreIsPGroupTwo (X : Subgroup G) : IsPGroup 2 (Work.GW2.pCoreIn 2 X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 ↥(sSup {N : Subgroup ↥X | N.Normal ∧ IsPGroup 2 N}) :=
    Sylow.sSup_of_normal (G := ↥X) (p := 2) _ (fun N hN => hN.2) (fun N hN => hN.1)
  have hcore : IsPGroup 2 (Work.GW2.pCore 2 ↥X) := hsup.to_le (Subgroup.normalCore_le _)
  exact hcore.map X.subtype

/-- **Bender 1981, §4, p. 227: `S₀ ≤ C_G(U)`**, given the §4 (7) identity
`O₂(H ⊓ M) = O₂(H)`.

This is the proof of `Work.CORE4.Case2S0_comm_U` with its single use of `Case2SevenFacts`
(the step `S₀ ≤ O₂(H)`, which passes through §4 (7) conjunct 1) replaced by the hypothesis
`hO2`.  Every other ingredient is available from `Case2Ctx` and `Case2PrePlus` alone. -/
theorem S0CentU_of_O2 (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B)
    (hO2 : Work.GW2.pCoreIn 2 (B.H ⊓ h.D.M) = Work.GW2.pCoreIn 2 B.H) :
    B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) := by
  have hplus : Work.GW2.Case2PrePlus B h.D := Case2PrePlusOfCtx G I hbc B h
  -- `S ≤ E = layerIn M` (§4 (9))
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M := S_le_layerIn h
  have hSleHM : (B.S : Subgroup G) ≤ h.D.M ⊓ B.H := by
    intro x hx
    exact ⟨Work.GW2.Case2Ctx.S_le_M h hx, B.S_le_H hx⟩
  have hS0leS : B.S0 ≤ (B.S : Subgroup G) := B.S0_le
  have hS0leHM : B.S0 ≤ h.D.M ⊓ B.H := by
    intro x hx
    have h := hSleHM (hS0leS hx)
    exact ⟨h.1, h.2⟩
  -- 1. Bender p. 224/227: `⁅K, S₀⁆ = ⊥`
  have hKS0 : ⁅h.D.K, B.S0⁆ = ⊥ := S0CentK I G hbc B h
  have hKS0' : h.D.K ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKS0
  -- 2. `B₀ = (U ⊓ M) ⊓ C(S ⊓ E)`, hence `⁅B₀, S₀⁆ = ⊥`
  have hB0le : h.D.B0 ≤
      Subgroup.centralizer ((((B.S : Subgroup G)) ⊓ Work.GW2.layerIn h.D.M : Subgroup G) : Set G) :=
    hplus.2.2 ▸ inf_le_right
  have hS0infE : B.S0 ≤ ((B.S : Subgroup G)) ⊓ Work.GW2.layerIn h.D.M := by
    intro x hx
    exact ⟨hS0leS hx, hSE (hS0leS hx)⟩
  have hB0S0' : h.D.B0 ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) :=
    hB0le.trans (Subgroup.centralizer_le (fun x hx => hS0infE hx))
  -- 3. `U ⊓ M = K ⊔ B₀` lies in `C_G(S₀)`
  have hUMS0' : B.U ⊓ h.D.M ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) := by
    rw [Work.GW2.Case2Pre.U_eq B h.D h.pre]
    exact sup_le hKS0' hB0S0'
  have hUMS0 : (B.U ⊓ h.D.M) ≤ Subgroup.normalizer ((B.S0 : Subgroup G) : Set G) :=
    hUMS0'.trans (Subgroup.centralizer_le_normalizer _)
  -- 4. `S₀ ⊴ S` (index two) and `H ⊓ M = (U ⊓ M) ⊔ S`, so `S₀ ⊴ H ⊓ M`
  have hS0S_normal : (B.S0.subgroupOf (B.S : Subgroup G)).Normal := by
    refine Subgroup.normal_of_index_eq_two ?_
    simpa [Subgroup.relIndex] using B.S0_index
  have hS_le_N : (B.S : Subgroup G) ≤ Subgroup.normalizer ((B.S0 : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer B.S0_le).mp hS0S_normal
  have hHM_le_N : h.D.M ⊓ B.H ≤ Subgroup.normalizer ((B.S0 : Subgroup G) : Set G) := by
    rw [Work.GW2.Case2Ctx.inter_H_M I h]
    exact sup_le hUMS0 hS_le_N
  have hS0_normal : (B.S0.subgroupOf (h.D.M ⊓ B.H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS0leHM).mpr hHM_le_N
  -- 5. `S₀ ≤ O₂(H ⊓ M) = O₂(H)` (§4 (7) conjunct 1, as a hypothesis)
  have hS0_pg : IsPGroup 2 (B.S0.subgroupOf (h.D.M ⊓ B.H)) := by
    have h1 : IsPGroup 2 ↥((B.S : Subgroup G).subgroupOf (h.D.M ⊓ B.H)) :=
      (B.S.isPGroup').of_equiv (Subgroup.subgroupOfEquivOfLe hSleHM).symm
    exact h1.to_le (Subgroup.subgroupOf_mono (h.D.M ⊓ B.H) hS0leS)
  have hS0_pcore : B.S0 ≤ Work.GW2.pCoreIn 2 (h.D.M ⊓ B.H) :=
    pcoreOfNormal hS0leHM hS0_normal hS0_pg
  have hS0_pcoreH : B.S0 ≤ Work.GW2.pCoreIn 2 B.H := by
    rw [← hO2, inf_comm]
    exact hS0_pcore
  -- 6. `O₂(H) ⊓ U = 1`
  have hXUbot : Work.GW2.pCoreIn 2 B.H ⊓ B.U = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxX, hxU⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨m, hm⟩ := (pcoreIsPGroupTwo (B.H)).exists_card_eq
    have h1 : orderOf x ∣ 2 ^ m := by
      rw [← hm]
      exact Subgroup.orderOf_dvd_natCard _ hxX
    have h2 : orderOf x ∣ Nat.card ↥B.U := Subgroup.orderOf_dvd_natCard B.U hxU
    have hodd : Odd (orderOf x) := Odd.of_dvd_nat B.U_odd h2
    obtain ⟨k, _hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h' | h'
      · exact h'
      · exact absurd (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp h')))
          (Nat.not_even_iff_odd.mpr (hk' ▸ hodd))
    exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])
  -- 7. `O₂(H)` normal in `H`, `U ◁ H` odd of coprime order, so `O₂(H) ≤ C_G(U)`
  have hXleH : Work.GW2.pCoreIn 2 B.H ≤ B.H := Subgroup.map_subtype_le _
  have hXsub : (Work.GW2.pCoreIn 2 B.H).subgroupOf B.H = Work.GW2.pCore 2 ↥B.H := by
    rw [Work.GW2.pCoreIn, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective B.H.subtype_injective _
  have hXn : ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H).Normal := by
    rw [hXsub]
    exact Work.GW2.pCore_normal 2 ↥B.H
  have hX_le_C : Work.GW2.pCoreIn 2 B.H ≤
      Subgroup.centralizer ((B.U : Subgroup G) : Set G) := by
    haveI : ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H).Normal := hXn
    haveI : (B.U.subgroupOf B.H).Normal := B.U_normal
    have hinf : ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H) ⊓ (B.U.subgroupOf B.H) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      have hyX : (y : G) ∈ Work.GW2.pCoreIn 2 B.H := by
        rwa [Subgroup.mem_subgroupOf] at hy1
      have hyU : (y : G) ∈ B.U := by rwa [Subgroup.mem_subgroupOf] at hy2
      refine Subtype.ext ?_
      have : (y : G) ∈ (⊥ : Subgroup G) := by
        rw [← hXUbot]
        exact ⟨hyX, hyU⟩
      simpa using this
    have hcomm : ⁅(Work.GW2.pCoreIn 2 B.H).subgroupOf B.H,
        (B.U.subgroupOf B.H)⁆ = ⊥ := by
      have h := Subgroup.commutator_le_inf ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H)
        (B.U.subgroupOf B.H)
      rw [hinf] at h
      exact le_bot_iff.mp h
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hx' : (⟨x, hXleH hx⟩ : ↥B.H) ∈ (Work.GW2.pCoreIn 2 B.H).subgroupOf B.H := by
      rwa [Subgroup.mem_subgroupOf]
    have hu' : (⟨u, B.U_le_H hu⟩ : ↥B.H) ∈ B.U.subgroupOf B.H := by
      rwa [Subgroup.mem_subgroupOf]
    have h1 : (⟨u, B.U_le_H hu⟩ : ↥B.H) * ⟨x, hXleH hx⟩ =
        ⟨x, hXleH hx⟩ * (⟨u, B.U_le_H hu⟩ : ↥B.H) :=
      Subgroup.mem_centralizer_iff.mp (hcen hx') _ hu'
    exact congrArg Subtype.val h1
  -- 8. Conclusion
  exact hS0_pcoreH.trans hX_le_C


/-- **Bender 1981, §4, p. 227: `S₀ ≤ C_G(U)`** — unconditional in the §4 configuration. -/
theorem S0CentU_of_ctx (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B) :
    B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) :=
  S0CentU_of_O2 I hbc h (SevenO2HM I G hbc B h)

/-- **The exceptional clause of Bender §4 (8), `I_U(s) ⊴ Ĥ`, does not occur** in the §4
configuration.  (`Case2NotInvNormal` from the proved `S₀ ≤ C_G(U)`.) -/
theorem not_Case2InvNormal_of_ctx (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B) :
    ¬ Work.GW2.Case2InvNormal B h.D :=
  Case2NotInvNormal G I hbc B h (S0CentU_of_ctx I hbc h)

end Work.CORE4
