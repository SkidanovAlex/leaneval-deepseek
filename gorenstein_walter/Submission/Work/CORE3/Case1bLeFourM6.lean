import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.Defs
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.RelIndexCentralizerFourGroup
import Submission.Work.CORE2A.normalizer_eq_of_coatom
import Submission.Work.BSW.Cases.K4.CardSup

set_option maxHeartbeats 800000

/-!
# `Work.CORE3.Case1bLeFourM6`

Bender 1981 §3, the last subcase of the analysis of the coset count `n = |I_Ĥ(y)| = 6` in the
`V = O₂(Ĥ)` of type (2,2) case.  Setting: `G` a minimal counterexample (`BenderCtx`), `B` a
Bender setup, `Case1 B`, `D : Case1bData B` (so `V = O₂(Ĥ)` is a four-group and `|S| = 8`),
`U = O(Ĥ) = O(H)` with `|U| = 3`, and `y` an involution outside `Ĥ` whose coset carries six
involutions (`cosetInvCount Ĥ y = 6`).

Write `Dd = Ĥ ⊓ Ĥ^y`, `VU = O₂(Ĥ) ⊔ O(Ĥ)`, `M = Dd ⊓ VU`.  This file shows `|M| ≠ 6`.

The mathematical argument (Bender 1981, p. 224; recorded in
`Submission/Work/CORE3/NOTES_LeFour_NeSix_status.md`):

* `Work.CORE3.Case1bDStructure` (applied with `4 ≤ 6`) gives `Dd ⊔ VU = Ĥ` and
  `|Dd : M| = 6`; with `|M| = 6` this forces `|Dd| = 36`.
* `|VU| = |O₂(Ĥ)| · |O(Ĥ)| = 4 · 3 = 12` (the two are of coprime order, and
  `O(Ĥ) ≤ C_G(O₂(Ĥ))`, `Work.CORE3.CentralizerPcoreEqVU`), and `|Ĥ : VU| = 6`
  (`Work.CORE3.relIndex_VU_Hhat`), so `|Ĥ| = 72`.
* Hence `[Ĥ : Dd] = 72 / 36 = 2`, and likewise (as `|Ĥ^y| = |Ĥ|` and `Dd ≤ Ĥ^y`) `[Ĥ^y : Dd] = 2`.
  So both `Ĥ` and `Ĥ^y` normalize `Dd`
  (`Work.BSW.Cases.K4.le_normalizer_of_two_mul_card`).
* `y ∉ Ĥ` together with `Ĥ` a coatom of a simple group gives `Ĥ^y ≠ Ĥ` and `Ĥ ⊔ Ĥ^y = ⊤`
  (a coatom is self-normalizing, `Work.CORE2A.normalizer_eq_of_coatom`).
* Therefore `N_G(Dd) ⊇ Ĥ ⊔ Ĥ^y = G`, i.e. `Dd ⊴ G`; simplicity forces `Dd = ⊥` or `Dd = ⊤`,
  both impossible since `|Dd| = 36`, `Dd ≤ Ĥ` and `Ĥ ≠ ⊤`.
-/

namespace Work.CORE3

open Subgroup

theorem Case1bLeFourM6 (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (h6 : Work.GW2.cosetInvCount B.Hhat y = 6) :
    Nat.card ↥((B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) ⊓ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U)) ≠ 6 := by
  classical
  intro hM6
  haveI : IsSimpleGroup G := hBc.simple
  set VU : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U with hVU
  set Dd : Subgroup G := B.Hhat ⊓ Work.GW2.conjSub y B.Hhat with hDd
  -- Bender's structural statement for `n ≥ 4`
  have hstruct := Work.CORE3.Case1bDStructure G I hBc B h1 D y hy2 hyH (by rw [h6]; norm_num)
  have hsup : Dd ⊔ VU = B.Hhat := by rw [hDd, hVU]; exact hstruct.1
  have hrel : (VU ⊓ Dd).relIndex Dd = 6 := by rw [hVU, hDd]; exact hstruct.2.1
  have hM6' : Nat.card ↥(VU ⊓ Dd) = 6 := by rw [inf_comm]; exact hM6
  -- `|Dd| = 6 · |Dd ⊓ VU| = 36`
  have hDcard : Nat.card ↥Dd = 36 := by
    have h := Subgroup.relIndex_mul_card (VU ⊓ Dd) Dd
    rw [hrel] at h
    simp only [inf_assoc, inf_idem] at h
    rw [hM6'] at h
    omega
  have hDleHhat : Dd ≤ B.Hhat := hDd ▸ inf_le_left
  have hDleHhaty : Dd ≤ Work.GW2.conjSub y B.Hhat := hDd ▸ inf_le_right
  -- `O(Ĥ)` centralizes `O₂(Ĥ)`
  have hUcV : B.U ≤ Subgroup.centralizer (Work.GW2.pCoreIn 2 B.Hhat : Set G) := by
    intro u hu
    have hmem : u ∈ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓
        B.Hhat := by
      rw [Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D]
      exact Subgroup.mem_sup_right hu
    exact hmem.1
  have hUN : B.U ≤ Subgroup.normalizer (Work.GW2.pCoreIn 2 B.Hhat : Set G) :=
    hUcV.trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U = ⊥ :=
    Work.BSW.Cases.K4.inf_eq_bot_of_coprime (by rw [D.four.1, hU3]; norm_num)
  -- `|VU| = 4 · 3 = 12`
  have hVUcard : Nat.card ↥VU = 12 := by
    rw [hVU, Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hUN hdisj, D.four.1, hU3]
  -- `|Ĥ| = 6 · |VU| = 72`
  have hHhatcard : Nat.card B.Hhat = 72 := by
    have hWle : Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U ≤ B.Hhat :=
      sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat (I.h26 G I.T.ft hBc B))
        (Work.CORE2A.thm26Concl_U_le_Hhat (I.h26 G I.T.ft hBc B))
    have h := Subgroup.relIndex_mul_card (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) B.Hhat
    rw [inf_eq_left.mpr hWle, Work.CORE3.relIndex_VU_Hhat G I hBc B h1 D] at h
    rw [← hVU, hVUcard] at h
    omega
  -- `[Ĥ : Dd] = 2`
  have hDrel : Dd.relIndex B.Hhat = 2 := by
    have h := Subgroup.relIndex_mul_card Dd B.Hhat
    rw [inf_eq_left.mpr hDleHhat, hDcard, hHhatcard] at h
    omega
  -- `Ĥ` and `Ĥ^y` are distinct
  have hyHhat' : Work.GW2.conjSub y B.Hhat ≠ B.Hhat := by
    intro heq
    have hmem : y ∈ Subgroup.normalizer (B.Hhat : Set G) := by
      rw [Subgroup.mem_normalizer_iff'']
      intro n
      have hiff := Work.CORE2A.mem_conjSub_iff (g := y) (K := B.Hhat) (x := n)
      rw [heq] at hiff
      exact hiff
    have hN : Subgroup.normalizer (B.Hhat : Set G) = B.Hhat :=
      Work.CORE2A.normalizer_eq_of_coatom B.Hhat_coatom le_rfl
        (Work.CORE2A.bSetup_Hhat_ne_bot B) Subgroup.le_normalizer
    rw [hN] at hmem
    exact hyH hmem
  -- hence they generate `G`
  have hltSup : B.Hhat < B.Hhat ⊔ Work.GW2.conjSub y B.Hhat := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hne
    have hle : Work.GW2.conjSub y B.Hhat ≤ B.Hhat :=
      le_sup_right.trans (le_of_eq hne.symm)
    have hcard : Nat.card ↥B.Hhat ≤ Nat.card ↥(Work.GW2.conjSub y B.Hhat) :=
      le_of_eq (Work.CORE2A.card_conjSub y B.Hhat).symm
    exact hyHhat' (Subgroup.eq_of_le_of_card_ge hle hcard)
  have htop : B.Hhat ⊔ Work.GW2.conjSub y B.Hhat = ⊤ :=
    B.Hhat_coatom.lt_iff.mp hltSup
  -- `Dd` is normalized by both maximal subgroups
  have hEH : B.Hhat ≤ Subgroup.normalizer (Dd : Set G) :=
    Work.BSW.Cases.K4.le_normalizer_of_two_mul_card hDleHhat (by rw [hDcard, hHhatcard])
  have hEH' : Work.GW2.conjSub y B.Hhat ≤ Subgroup.normalizer (Dd : Set G) :=
    Work.BSW.Cases.K4.le_normalizer_of_two_mul_card hDleHhaty
      (by rw [hDcard, Work.CORE2A.card_conjSub y B.Hhat, hHhatcard])
  have hDnorm : Dd.Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
    rw [← htop]
    exact sup_le hEH hEH'
  -- contradiction with simplicity
  haveI : Dd.Normal := hDnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Dd with hbot | htopD
  · rw [hbot, Subgroup.card_bot] at hDcard
    omega
  · exact (Work.CORE2A.bSetup_Hhat_ne_top B) (top_le_iff.mp (htopD ▸ hDleHhat))

end Work.CORE3
