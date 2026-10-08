import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.bgData_of_setup
import Submission.Work.CORE3.Case1aThmCInputs
import Submission.Work.CORE3.SylowFromLocalControl
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.Case1aBFpf
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.ncard_invSet_eq_one_of_le_centralizer
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aBothInvert
import Submission.Work.CORE3.Case1aBFitting
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.LeCentralizerOfCoprimeNormal
import Submission.Work.CORE2A.odd_subgroup_le_oddCoreIn
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.DSTR.map_fittingPiIn_le
import Submission.Work.DSTR.D16Basic
import Submission.Work.CORE3.c1aDirMaxInv
import Submission.Work.CORE3.c1aDirInternalDirect
import Submission.Work.CORE3.c1aDirIndexCoprime
import Submission.Work.CORE3.c1aDirBcCoprime
import Submission.Work.CORE3.c1aDirCentS

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.CORE3

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Design pass 4 §1: the hypotheses of Bender–Glauberman Theorem C (`Work.GW2.BGThmCProp`) in
the subcase `Ĥ = H`, assembled from the §3 data.  Deliverable `Work.CORE3.Case1aThmCInputsProp`.

This is the amended statement of `Work.CORE3.Case1aThmCInputs`: its prover found that the
elementwise commutation `[O_p(U), C_U(S)] = 1` — Bender's `C_U(t₁) = C_U(S) × O_p(U)` — is not
forced by `Case1aA7Prop`/`Case1aMDataProp`, and it is now supplied as
`hDir : Case1aDirectProp`.

`BG` is the `BGData` of `(B.S, B.S0, B.t, D.t1, D.t2)`; `gen : S₀ = ⟨t₁t₂⟩` is
`Work.CORE3.Case1aThmCGen`, already proved in `Submission/Work/CORE3/Case1aThmCInputs.lean`
(import that module for it and for the helpers `c1aU_eq_fitting_sup_B`,
`c1aFittingIn_eq_sup_three`, `c1aPcoreIn_le_fittingIn`, `c1aIsPGroup_pCoreIn`; do **not** use the
stale top-level `Case1aThmCInputs` there, and note that `c1aPcommF3` there is closed by `sorry`,
so re-derive `⁅O_3(U), F_{3'}(U)⁆ = ⊥` yourself — both are normal subgroups of the nilpotent
`F(U)` of coprime order, so their commutator lies in their intersection `= ⊥`).

`K₁ = I_U(t₁)`, `K₂ = I_U(t₂)` are the maximal odd subgroups of `H = C(t)` inverted by `t₁`,
`t₂` (Case (1) makes `I_U(tᵢ)` Hall in `F(U)`; `hInv` gives that both `tᵢ` invert
`F_{3'}(U)`; since `t₂` centralizes `B` and inverts `F(U)` one gets `K₂ ⊇ F(U)` and
`K₁ ∩ K₂ = F_{3'}(U)`).  `U = (B₁ ∩ K₂) × B K`: `hDir` gives `B₁ = C_U(t₁) = B ⊔ O_p(U)` with
elementwise commutation (so `B₁ ∩ K₂ = O_p(U)`, using `B ∩ O_p(U) = ⊥`), `hMD` gives `B ≤ M`,
`B ∩ M = O(M)`, `U ∩ M = P₀ ⊔ B` and `N_G(X) ≤ M` for `1 ≠ X ≤ B`.  `BK` is Frobenius with
kernel `K` (`hBpf`); `(|K|, |G:H|) = 1` via `Work.CORE3.SylowFromLocalControlProp` applied to
`R = O_r(U)` for primes `r ∣ |K|` (using Case (1)'s local control and `r ∤ |B|`); and `B' ≠ B`
because `B ≠ ⊥` is solvable (Feit–Thompson, `I.T.ft`). -/
theorem Case1aThmCInputsDir (I : Case1Inputs) (hFr : Case1aFrattiniProp) (hAb : Case1aAbelianProp)
    (hA7 : Case1aA7Prop) (hInv : Case1aBothInvertProp) (hBpf : Case1aBFpfProp)
    (hMD : Case1aMDataProp) (hDir : Case1aDirectProp) : Case1aThmCInputsProp := by
  intro G _instG _finG hFT hCtx B hCase1 hHhat D
  classical
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  haveI : IsSimpleGroup G := hCtx.simple
  -- ## Step 0: Bender's §3 setup (a Sylow `p`-subgroup of `C_U(S)`, a maximal subgroup `M`).
  obtain ⟨n, hn, hdih⟩ := SylowDihedral G hCtx B
  have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
    obtain ⟨e⟩ := hdih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN hIdx
    have hbot : N ≠ ⊥ := by
      intro hh
      rw [hh, Subgroup.index_bot] at hIdx
      have h2 : 2 * n ≤ Nat.card G := by
        have h := Subgroup.card_le_card_group (B.S : Subgroup G)
        rwa [hcardS] at h
      omega
    have htop : N ≠ ⊤ := by intro hh; rw [hh, Subgroup.index_top] at hIdx; omega
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · exact hbot h1
    · exact htop h1
  have hclass : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    (I.T.fus G B.S n hn hdih hnoN).1
  set Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hBcdef
  have hpB : D.p ∣ Nat.card Bc := by
    by_contra hpdvd
    have hrel : ¬ D.p ∣ (⊥ : Subgroup G).relIndex Bc := by rwa [Subgroup.relIndex_bot_left]
    exact (hFr G hFT hCtx B hCase1 hHhat D ⊥ bot_le IsPGroup.of_bot hrel).2.2 rfl
  obtain ⟨P2, hP2le, hP2grp, hP2ndvd⟩ := bfpf_exists_pSubgroup_le_of_dvd D.p Bc hpB
  have hP2Hhat : P2 ≤ B.Hhat := hP2le.trans (le_trans inf_le_left (Work.CORE2A.bSetup_U_le_Hhat B))
  have hNHat_ne : Subgroup.normalizer (P2 : Set G) ≠ ⊤ := by
    intro htop
    haveI : P2.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P2 with h | h
    · exact (hFr G hFT hCtx B hCase1 hHhat D P2 hP2le hP2grp hP2ndvd).2.2 h
    · rw [h] at hP2Hhat
      exact B.Hhat_coatom.ne_top (top_le_iff.mp hP2Hhat)
  obtain ⟨M, hMcoat, hNM⟩ := bfpf_exists_isCoatom_le_of_ne_top _ hNHat_ne
  obtain ⟨hSM, hV2E, _hiso, hS8, hP0card⟩ :=
    hA7 G hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  obtain ⟨hBM, hBcM, hUM, hNX⟩ :=
    hMD G hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  have hP2ne : P2 ≠ ⊥ := (hFr G hFT hCtx B hCase1 hHhat D P2 hP2le hP2grp hP2ndvd).2.2
  have hBne : Bc ≠ ⊥ := fun h => hP2ne (le_bot_iff.mp (h ▸ hP2le))
  have hP0pg : IsPGroup D.p (pCoreIn D.p B.U ⊓ M : Subgroup G) :=
    (c1aIsPGroup_pCoreIn D.p B.U).to_le inf_le_left
  have hp3 : D.p = 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP0pg
    have hk3 : D.p ^ k = 3 := by rw [← hk, hP0card]
    have hk1 : k ≠ 0 := by rintro rfl; simp at hk3
    have hd : D.p ∣ 3 := by
      have h := dvd_pow_self D.p hk1
      rwa [hk3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact absurd h1 D.hp.ne_one
    · exact h3
  have hgen := Case1aThmCGen I hFr hA7 G hFT hCtx B hCase1 hHhat D
  -- ## Step 1: `BG` and the auxiliary identifications
  let BG : BGData G :=
    { S := B.S, n := n, two_le := hn, dih := hdih, oneClass := hclass
      S0 := B.S0, S0_le := B.S0_le, S0_cyclic := B.S0_cyclic, S0_index := B.S0_index
      t := B.t, t_mem := B.t_mem, t_order := B.t_order
      t1 := D.t1, t2 := D.t2, t1_mem := D.t1_mem, t2_mem := D.t2_mem
      t1_nmem := D.t1_nmem, t2_nmem := D.t2_nmem, t1_order := D.t1_order
      t2_order := D.t2_order, gen := hgen }
  -- `C_G(S) = C_G(t₁) ⊓ C_G(t₂)` (from `S = ⟨t₁,t₂⟩`)
  have hCentS : Subgroup.centralizer ((B.S : Subgroup G) : Set G) =
      Subgroup.centralizer ({D.t1} : Set G) ⊓ Subgroup.centralizer ({D.t2} : Set G) :=
    c1aDirCentS B D hgen
  -- hence `BG.B = Bc`
  have hBGB : (BG.B : Subgroup G) = Bc := by
    show (B.U ⊓ Subgroup.centralizer ({D.t1} : Set G)) ⊓
        (B.U ⊓ Subgroup.centralizer ({D.t2} : Set G)) = Bc
    rw [hBcdef, hCentS, inf_inf_inf_comm, inf_idem]
  -- `Bc ≤ U`
  have hBc_le_U : Bc ≤ B.U := by rw [hBcdef]; exact inf_le_left
  -- the easy inclusion `Bc ≤ BG.B`
  have hBc_le_BGB : Bc ≤ (BG.B : Subgroup G) := by rw [hBGB]
  -- `BG.B ≤ U`
  have hBGB_le_U : (BG.B : Subgroup G) ≤ B.U := (le_of_eq hBGB).trans hBc_le_U
  -- ## Step 2: `K = F_{3'}(U) ≠ ⊥` (needed for the Frobenius clause)
  have hKne : fittingPiIn ({3}ᶜ) B.U ≠ ⊥ := by
    intro hKbot
    -- if `F_{3'}(U) = ⊥` then `F(U) = O_p(U)` and `U = O_p(U) ⊔ Bc = C_U(t₁)`
    have hFU : fittingIn B.U = pCoreIn D.p B.U := by
      rw [c1aFittingIn_eq_sup_three B.U, hp3, hKbot, bot_sup_eq]
    have hUeq : B.U = pCoreIn D.p B.U ⊔ Bc := by
      rw [← hFU, hBcdef]
      exact c1aU_eq_fitting_sup_B I G hFT hCtx B hCase1
    have hCt1 : B.U ≤ Subgroup.centralizer ({D.t1} : Set G) := by
      have hdir1 : B.U ⊓ Subgroup.centralizer ({D.t1} : Set G) = Bc ⊔ pCoreIn D.p B.U :=
        (hDir G hFT hCtx B hCase1 hHhat D).1
      rw [hUeq, sup_comm, ← hdir1]
      exact inf_le_right
    -- so `t₁ ∈ S ⊓ C_G(U) = O₂(Ĥ)`
    have ht1c : D.t1 ∈ Subgroup.centralizer (B.U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact ((Subgroup.mem_centralizer_iff.mp (hCt1 hu)) D.t1 (Set.mem_singleton D.t1)).symm
    have ht1V : D.t1 ∈ pCoreIn 2 B.Hhat := by
      rw [← (I.h26 G hFT hCtx B).2.1]
      exact ⟨D.t1_mem, ht1c⟩
    -- Theorem 2.6: first alternative puts `t₁ ∈ S₀`; the second contradicts `|S| = 8`
    rcases (I.h26 G hFT hCtx B).2.2 with ⟨hle, -⟩ | ⟨hfour, hrel6, -⟩
    · exact D.t1_nmem (hle ht1V)
    · rw [hHhat] at hrel6 hfour
      have h26id : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) = pCoreIn 2 B.H := by
        rw [(I.h26 G hFT hCtx B).2.1]
        exact congrArg (fun K => pCoreIn 2 K) hHhat
      have hV_le_S : pCoreIn 2 B.H ≤ (B.S : Subgroup G) := by
        rw [← h26id]; exact inf_le_left
      have hV_le_H : pCoreIn 2 B.H ≤ B.H := le_trans hV_le_S (Work.CORE2A.bSetup_S_le_H B)
      have hU_le_H : B.U ≤ B.H := Work.CORE2A.bSetup_U_le_H B
      have hH_le_NU : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
        le_normalizer_map_subtype_of_normal' (K := B.H) (N := oddCore ↥B.H) inferInstance
      have hS_le_NU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
        (Work.CORE2A.bSetup_S_le_H B).trans hH_le_NU
      have hV_le_NU : pCoreIn 2 B.H ≤ Subgroup.normalizer (B.U : Set G) := hV_le_H.trans hH_le_NU
      have hUV : B.U ⊓ pCoreIn 2 B.H = ⊥ := by
        have h : B.U ⊓ pCoreIn 2 B.H ≤ B.U ⊓ (B.S : Subgroup G) := inf_le_inf le_rfl hV_le_S
        rw [Work.CORE2A.inf_U_S_eq_bot B] at h
        exact le_bot_iff.mp h
      have hHsup : B.U ⊔ (B.S : Subgroup G) = B.H := H_eq_U_sup_S G I.T hCtx B
      have hcardH : Nat.card ↥B.H = Nat.card ↥B.U * 8 := by
        rw [← hHsup, Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hS_le_NU
          (Work.CORE2A.inf_U_S_eq_bot B), hS8]
      have hcardW : Nat.card ↥(pCoreIn 2 B.H ⊔ B.U) = Nat.card ↥B.U * 4 := by
        rw [sup_comm, Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hV_le_NU hUV,
          hfour.1]
      have hmul := Subgroup.relIndex_mul_card (H := pCoreIn 2 B.H ⊔ B.U) (K := B.H)
      rw [inf_eq_left.mpr (sup_le hV_le_H hU_le_H), hcardW, hcardH] at hmul
      have hpos : 0 < Nat.card ↥B.U * 4 := Nat.mul_pos Nat.card_pos (by norm_num)
      have hkey : (pCoreIn 2 B.H ⊔ B.U).relIndex B.H * (Nat.card ↥B.U * 4)
          = 2 * (Nat.card ↥B.U * 4) := by rw [hmul]; ring
      have h2 : (pCoreIn 2 B.H ⊔ B.U).relIndex B.H = 2 :=
        Nat.eq_of_mul_eq_mul_right hpos hkey
      omega
  -- ## Step 3: the six clauses
  refine ⟨BG, rfl, rfl, rfl, rfl, rfl, fittingPiIn ({3}ᶜ) B.U, fittingIn B.U,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `K₁ = F_{3'}(U)` is the largest odd subgroup of `H` inverted by `t₁`
    exact (c1aDirMaxInv I hFr hAb hA7 hBpf hMD hDir G hFT hCtx B hCase1 hHhat D).1
  · -- `K₂ = F(U)` is the largest odd subgroup of `H` inverted by `t₂`
    exact (c1aDirMaxInv I hFr hAb hA7 hBpf hMD hDir G hFT hCtx B hCase1 hHhat D).2
  · -- `U = (B₁ ∩ K₂) × (BK)`
    exact c1aDirInternalDirect I hFr hAb hA7 hBpf hMD hDir G hFT hCtx B hCase1 hHhat D
  · -- `(|K|, |G:H|) = 1`
    exact c1aDirIndexCoprime I hFr hAb hA7 hBpf hMD hDir G hFT hCtx B hCase1 hHhat
      (c1aDirBcCoprime hBpf G hFT hCtx B hCase1 hHhat)
  · -- `B' ≠ B`: `BG.B = Bc ≠ ⊥` has odd order, hence is solvable (Feit–Thompson)
    intro hcomm
    have hBGB_ne : (BG.B : Subgroup G) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hBc_le_BGB
      exact hBne (le_bot_iff.mp hBc_le_BGB)
    haveI : Group.IsSolvable ↥B.U := hFT ↥B.U (Work.CORE2A.bSetup_U_odd B)
    set K : Subgroup ↥B.U := (BG.B : Subgroup G).subgroupOf B.U with hKdef
    have hmapK : K.map B.U.subtype = (BG.B : Subgroup G) := by
      rw [hKdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBGB_le_U]
    have hKne' : K ≠ ⊥ := by
      intro hbot
      exact hBGB_ne (by rw [← hmapK, hbot, Subgroup.map_bot])
    have hlt : ⁅K, K⁆ < K := Group.IsSolvable.commutator_lt_of_ne_bot hKne'
    have hEq : ⁅K, K⁆ = K := by
      apply Subgroup.map_injective (Subgroup.subtype_injective B.U)
      rw [Subgroup.map_commutator, hmapK]
      exact hcomm
    exact absurd hEq (ne_of_lt hlt)
  · -- the Frobenius clause
    intro _
    -- normality of `K₁ = F_{3'}(U)` in `U`
    have hU_le_NK1 : B.U ≤ Subgroup.normalizer (fittingPiIn ({3}ᶜ) B.U : Set G) := by
      have hchar : (piCore ({3}ᶜ) ↥(fitting ↥B.U)).Characteristic :=
        Work.DSTR.FittingPiImg.piCore_characteristic (G := ↥(fitting ↥B.U)) ({3}ᶜ)
      haveI hAnorm : (fitting ↥B.U).Normal := inferInstance
      haveI hcore : (Subgroup.map (fitting ↥B.U).subtype
          (piCore ({3}ᶜ) ↥(fitting ↥B.U))).Normal :=
        ConjAct.normal_of_characteristic_of_normal
      exact le_normalizer_map_subtype_of_normal' (K := B.U) hcore
    have hK1_le_FU : fittingPiIn ({3}ᶜ) B.U ≤ fittingIn B.U :=
      bfpf_fittingPiIn_le_fittingIn _ _
    -- `Bc ⊓ F(U) = ⊥` (`Case1aBFittingProp`)
    have hBFit : Bc ⊓ fittingIn B.U = ⊥ :=
      Case1aBFitting I (Case1aSetup I) hFr hAb hA7 hMD G hFT hCtx B hCase1 hHhat
    have hF_eq : (fittingPiIn ({3}ᶜ) B.U ⊓ fittingIn B.U : Subgroup G) = fittingPiIn ({3}ᶜ) B.U :=
      inf_eq_left.mpr hK1_le_FU
    refine ⟨le_sup_right, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · -- `(K₁ ∩ K₂) ⊴ (BG.B ⊔ (K₁ ∩ K₂))`
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ?_
      rw [hF_eq]
      exact sup_le ((le_of_eq hBGB).trans (hBc_le_U.trans hU_le_NK1)) Subgroup.le_normalizer
    · -- `BG.B ⊓ (K₁ ∩ K₂) = ⊥`
      rw [hBGB, hF_eq]
      refine le_bot_iff.mp ((le_inf inf_le_left (inf_le_right.trans hK1_le_FU)).trans
        (le_of_eq hBFit))
    · -- `K₁ ∩ K₂ ≠ ⊥`
      rw [hF_eq]; exact hKne
    · -- `BG.B ≠ ⊥`
      intro hbot
      rw [hBGB] at hbot
      exact hBne hbot
    · -- the fixed-point-freeness
      intro b hb hbne
      rw [hBGB] at hb
      rw [hF_eq]
      exact hBpf G hFT hCtx B hCase1 hHhat b hb hbne

end Work.CORE3

open Work.GW2

/-- The same lemma, mirrored at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Case1aThmCInputsDir` (the name the area requests) and as
`Work.CORE3.Work.CORE3.Case1aThmCInputsDir` (the skeleton's namespace layout). -/
theorem Case1aThmCInputsDir (I : Case1Inputs) (hFr : Case1aFrattiniProp) (hAb : Case1aAbelianProp)
    (hA7 : Case1aA7Prop) (hInv : Case1aBothInvertProp) (hBpf : Case1aBFpfProp)
    (hMD : Case1aMDataProp) (hDir : Case1aDirectProp) : Case1aThmCInputsProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aThmCInputsDir I hFr hAb hA7 hInv hBpf hMD hDir

end Work.CORE3
