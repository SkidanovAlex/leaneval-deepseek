import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.CORE3.Case1bCount
import Submission.Work.CORE3.Case1bOne
import Submission.Work.CORE3.Case1bFive
import Submission.Work.CORE3.Case1bSetup
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.CosetInvCountNeSixOf
import Submission.Work.CORE3.CosetPairCountFour
import Submission.Work.CORE3.CommutingPairTallyCosets
import Submission.Work.CORE3.CommutingPairTallyCentralizers
import Submission.Work.CORE3.InvolutionCentralizerCount
import Submission.Work.CORE3.CommutingInvolsVsharp
import Submission.Work.CORE3.CommutingInvolsOutsideV
import Submission.Work.CORE3.SevenNoInvolCentralizer
import Submission.Work.CORE3.Case1bSevenLeFour
import Submission.Work.CORE3.Case1bSevenInvInI
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.SixInvSetMulTable
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.J4.J4DTriv
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.CORE3.J4.J4CosetStep
import Submission.Work.CORE3.J4.J4U3ConjK
import Submission.Work.CORE3.J4U3V18Aux.PcoreConjCentralizer
import Submission.Work.CORE3.D23.Core23A
import Submission.Work.CORE3.D23.InvolActionUniform
import Submission.Work.CORE3.D23.FittingFaithfulFour
import Submission.Work.CORE3.Case1aMData2

/-!
# `Work.CORE3.J4U3V18Aux.LcFailsOfCardU`

Bender 1981, §3, p. 224, the missing input of step (7): in the configuration
`G` a minimal counterexample, `B` a Bender setup and `V = O₂(Ĥ)` of type `(2,2)`
(`D : Case1bData B`), if `|U| = |O(Ĥ)| ≠ 3` then local control — clause (ii) of
Bender's Theorem 2.10, case (1) — must fail:

`∃ Y ≠ ⊥, Y ≤ F(U),  ¬ (N_G(Y) ≤ Ĥ)`.

Equivalently (contrapositive): clause (1)(ii) together with the `(1b)`-data forces `|U| = 3`.

## Route

* Clause (ii) is the hypothesis we negate; under it (this is `hlc` below) the first clause of
  `Case1 B` is also available for free: every `s ∈ S ∖ S₀` is an involution (`S ≅ D₈`, `|S| = 8`)
  lying in `Ĥ`; if `s ∈ V = O₂(Ĥ)` then `s` centralises `U` (Theorem 2.6) so `I_U(s) = 1` is a
  Hall subgroup of `F(U)`, and if `s ∉ V` then `D.inv` identifies `invSet B.U s` with the Hall
  subgroup `D.K`.  Hence `Case1 B` holds, and Bender's §3 (1b)-analysis applies.
* Bender's step (7) `b₄ ≠ 0 → |U| = 3` is supplied by the *repaired* proof
  `Work.CORE3.D23.J4U3V18s` (design pass 23 §A), whose only missing leaf is
  `CardUOfFittingThreeProp`; that leaf is proved here as
  `card_U_eq_three_of_card_fittingIn_eq_three` (`U/C_U(F(U)) ↪ Aut(C₃)`, Bender 1.2 / P. Hall).
* The counting input `bₙ = 0` for `n ≥ 5` needs `cosetInvCount Ĥ y ≤ 4`; the module
  `Work.CORE3.CosetInvCountNeSix` is tainted (it cites the `sorry` of `BenderSevenU3`), so the
  clean route `Work.CORE3.cosetInvCount_ne_six_of` + `Work.CORE3.BenderSixNeSixAuxS` + the
  config-to-`|Ĥ ⊓ Ĥ^y| = 6` conversion (`card_inf_conjSubOfThree`, itself sorry-free) is used
  instead, in `cosetInvCount_ne_six_clean`.
* With `Case1 B` and the counting results available, `Case1bEightNineProp` is reproved
  (`case1bEightNine_of_lc`), and the arithmetic of `Work.CORE3.Case1bNumerics` then yields
  `|U| = 3`, contradicting `hU`.
-/

namespace Work.CORE3.J4U3V18Aux

open Subgroup
open Work.GW2

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

/-- **Bender 1.2 (P. Hall) transported to `F(U)`.**  `|F(U)| = 3 ⟹ |U| = 3`.

`U = O(Ĥ)` has odd order, hence is solvable; `U` acts on the characteristic subgroup
`F(U) = fittingIn B.U` of order `3`, whose automorphism group has exponent `2`
(`Work.CORE3.mdata2_mulAut_sq_eq_one_of_card_three`); as `U` is odd the action is trivial, so
`U ≤ C_U(F(U))`.  Fitting's self-centralising lemma
(`OddOrder.GroupTheory.centralizer_fitting_le_fitting`) then gives `U ≤ F(U)`. -/
theorem card_U_eq_three_of_card_fittingIn_eq_three {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (hFit : Nat.card (Work.GW2.fittingIn B.U) = 3) :
    Nat.card B.U = 3 := by
  classical
  -- `U ≤ N_G(F(U))`
  have hUleN : B.U ≤ Subgroup.normalizer ((Work.GW2.fittingIn B.U) : Set G) := by
    have hh := Work.CORE3.c1aLe_normalizer_map_subtype (K := B.U)
      (N := Work.GW2.fitting ↥B.U) (Subgroup.normalCore_normal _)
    simpa [Work.GW2.fittingIn] using hh
  -- every `u ∈ U` centralises `F(U)`
  have hcen : ∀ u ∈ B.U, ∀ a ∈ Work.GW2.fittingIn B.U, u * a = a * u := by
    intro u hu a ha
    have hodd : Odd (orderOf u) :=
      (Work.CORE2A.bSetup_U_odd B).of_dvd_nat (Subgroup.orderOf_dvd_natCard B.U hu)
    have hh : u * a * u⁻¹ = a := Work.CORE3.mdata2_conj_eq_self_of_odd_of_card_three
      (Q := Work.GW2.fittingIn B.U) (hUleN hu) hFit hodd a ha
    have h2 : (u * a * u⁻¹) * u = a * u := congrArg (fun z => z * u) hh
    rwa [show (u * a * u⁻¹) * u = u * a from by group] at h2
  -- Fitting self-centralising
  haveI : Group.IsSolvable ↥B.U := OddOrder.feitThompson (Work.CORE2A.bSetup_U_odd B)
  have hfit_eq : OddOrder.Isaacs.Ch01.fitting ↥B.U = Work.GW2.fitting ↥B.U :=
    (Work.CORE2A.fitting_eq_isaacsFitting (G := ↥B.U)).symm
  have hle : Subgroup.centralizer ((Work.GW2.fitting ↥B.U : Subgroup ↥B.U) : Set ↥B.U) ≤
      Work.GW2.fitting ↥B.U := by
    have hh := OddOrder.GroupTheory.centralizer_fitting_le_fitting (G := ↥B.U)
    rwa [hfit_eq] at hh
  have hUleF : ∀ u : ↥B.U, u ∈ Work.GW2.fitting ↥B.U := by
    intro u
    apply hle
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (hcen u u.2 a (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)).symm
  -- hence `⊤ ≤ F(↥U)`, and `|U| = |F(↥U)| = 3`
  have htop : (⊤ : Subgroup ↥B.U) ≤ Work.GW2.fitting ↥B.U := fun u _ => hUleF u
  have hEq : Work.GW2.fitting ↥B.U = ⊤ := top_le_iff.mp htop
  have hcardFit : Nat.card ↥(Work.GW2.fitting ↥B.U) = 3 := by
    rw [← Subgroup.card_map_of_injective (K := Work.GW2.fitting ↥B.U) (f := B.U.subtype)
      B.U.subtype_injective]
    exact hFit
  have h1 : Nat.card ↥B.U = Nat.card ↥(Work.GW2.fitting ↥B.U) := by
    rw [hEq]
    exact (Nat.card_congr (Subgroup.topEquiv (G := ↥B.U)).toEquiv).symm
  rw [h1, hcardFit]

/-- **Bender (6) for `n = 6`**, the *configuration* half, in a module-local copy of
`Work.CORE3.BenderSixNeSixAuxS` (which sits in `Submission/Work/CORE3/CosetInvCountNeSix.lean`,
a module currently inside an import cycle with `Work.CORE3.BenderSeven`; copying its proof here
keeps this file buildable).  If the coset of the involution `y ∉ Ĥ` carries at least five
involutions (hence, by (5) and `n ≠ 5`, exactly six), then some involution `z = k * y` of that
coset inverts a nontrivial odd-order subgroup `X ≤ Ĥ` whose `G`-centralizer and `G`-normalizer
have even order, and `X` is inverted by an involution of `Ĥ` as well (Bender's `N_Ĥ(X)`
hypothesis for step (7), needed by `Work.CORE3.D23.J4U3V18s`). -/
theorem benderSixNeSixConfig (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1}) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → 5 ≤ Work.GW2.cosetInvCount B.Hhat y →
      ∃ z : G, orderOf z = 2 ∧ (∃ k ∈ B.Hhat, z = k * y) ∧
        ∃ X : Subgroup G, X ≤ B.Hhat ∧ X ≠ ⊥ ∧ Odd (Nat.card ↥X) ∧ Work.GW2.Inverts z X ∧
          Even (Nat.card (Subgroup.centralizer (X : Set G))) ∧
          Even (Nat.card (Subgroup.normalizer (X : Set G))) ∧
          (∃ s ∈ B.Hhat, orderOf s = 2 ∧ Work.GW2.Inverts s X) := by
  intro y hy2 hyH hbig
  have hy : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hyne : y ≠ 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).2
  have hle6 : Work.GW2.cosetInvCount B.Hhat y ≤ 6 :=
    Work.CORE3.cosetInvCount_le_six G I h B h1 D h5 y hy2 hyH
  have hne5 : Work.GW2.cosetInvCount B.Hhat y ≠ 5 :=
    Work.CORE3.CosetInvCountNeFive G I h B h1 D h5 y hy2 hyH
  have h6 : Work.GW2.cosetInvCount B.Hhat y = 6 := by omega
  obtain ⟨a, b1, b2, ha, ha3, hb1, hb1o, hb2, hb2o, hb12⟩ :=
    Work.CORE3.SixInvSetElements G I h B h1 D h5 y hy2 hyH h6
  obtain ⟨hconj1, hcube⟩ :=
    Work.CORE3.SixInvSetMulTable G I h B h1 D h5 y hy2 hyH h6 a b1 b2 ha ha3 hb1 hb1o hb2 hb2o hb12
  -- `y` inverts `a`, and `y` inverts (hence centralizes) the involution `b₁`
  have hyinv : y⁻¹ = y := inv_eq_of_sq_eq_one hy
  have hb1_sq : b1 * b1 = 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1o).1
  have hb1_ne : b1 ≠ 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1o).2
  have hb1inv : b1⁻¹ = b1 := inv_eq_of_sq_eq_one hb1_sq
  have ha_inv : y * a * y⁻¹ = a⁻¹ := by
    rw [hyinv]; exact ha.2
  have hya : y * b1 * y⁻¹ = b1 := by
    rw [hyinv, hb1.2, hb1inv]
  have hya' : y * b1 = b1 * y := by
    have hh := congrArg (fun z => z * y) hya
    simpa [mul_assoc] using hh
  -- the auxiliary involution `w = b₁ * y`
  have hw2 : (b1 * y) * (b1 * y) = 1 := by
    calc (b1 * y) * (b1 * y) = b1 * (y * b1) * y := by group
      _ = b1 * (b1 * y) * y := by rw [hya']
      _ = (b1 * b1) * (y * y) := by group
      _ = 1 := by rw [hb1_sq, hy, mul_one]
  have hw1 : b1 * y ≠ 1 := by
    intro hcon
    have hh : y = b1 := by
      have h2 : b1 * (b1 * y) = b1 := by
        simpa using congrArg (fun z => b1 * z) hcon
      rw [← mul_assoc, hb1_sq, one_mul] at h2
      exact h2
    exact hyH (by rw [hh]; exact hb1.1)
  have hwa : (b1 * y) * a * (b1 * y)⁻¹ = a := by
    have h1 : (b1 * y) * a * (b1 * y)⁻¹ = b1 * (y * a * y⁻¹) * b1 := by
      rw [mul_inv_rev, hyinv, hb1inv]
      group
    rw [h1, ha_inv]
    have h2 : b1 * a⁻¹ * b1 = (b1 * a * b1)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hb1inv, mul_assoc]
    rw [h2, hconj1, inv_inv]
  refine ⟨y, hy2, ⟨1, B.Hhat.one_mem, by rw [one_mul]⟩, Subgroup.zpowers a,
    Subgroup.zpowers_le.mpr ha.1, ?_, ?_, Work.CORE3.J4.inverts_zpowers_of ha_inv, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : a ∈ (Subgroup.zpowers a : Subgroup G) := Subgroup.mem_zpowers a
    rw [hbot] at hmem
    have ha1 : a = 1 := by simpa using hmem
    have : orderOf a = 1 := by rw [ha1]; exact orderOf_one
    omega
  · rw [Nat.card_zpowers, ha3]
    decide
  · have hmem : b1 * y ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hconjm : MulAut.conj (b1 * y) a = a := by
        rw [MulAut.conj_apply]; exact hwa
      have hpow : (b1 * y) * a ^ n * (b1 * y)⁻¹ = a ^ n := by
        have h1 : (b1 * y) * a ^ n * (b1 * y)⁻¹ = (MulAut.conj (b1 * y)) (a ^ n) := by
          rw [MulAut.conj_apply]
        rw [h1, map_zpow, hconjm]
      calc a ^ n * (b1 * y) = ((b1 * y) * a ^ n * (b1 * y)⁻¹) * (b1 * y) := by rw [hpow]
        _ = (b1 * y) * a ^ n := by group
    exact Work.CORE3.J4.even_card_centralizer_of_involution (X := Subgroup.zpowers a)
      (w := b1 * y) hw2 hw1 hmem
  · exact Work.CORE3.J4.even_card_normalizer_of_inverts (X := Subgroup.zpowers a) hy hyne
      (Work.CORE3.J4.inverts_zpowers_of ha_inv)
  · exact ⟨b1, hb1.1, hb1o,
      Work.CORE3.J4.inverts_zpowers_of (by rw [hb1inv]; exact hconj1)⟩

/-- **Bender (7), second half**, in a module-local copy of `Work.CORE3.card_inf_conjSubOfThree`
(which sits in the import-cycle module `Work.CORE3.BenderSevenD6`): given `|U| = 3` and that the
coset `Ĥy` carries exactly four involutions, the intersection `Ĥ ⊓ Ĥ^y` has order `6`. -/
theorem cardInfConjSubOfThree
    {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (X : Subgroup G) (hXle : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : Work.GW2.Inverts y X)
    (hCeven : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hNeven : Even (Nat.card (Subgroup.normalizer (X : Set G))))
    (hU3 : Nat.card B.U = 3) (hy4 : Work.GW2.cosetInvCount B.Hhat y = 4) :
    Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) = 6 := by
  classical
  set W : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U with hW
  set Dsub : Subgroup G := B.Hhat ⊓ Work.GW2.conjSub y B.Hhat with hDsub
  have hWrel : W.relIndex B.Hhat = 6 := by
    rw [hW]; exact Work.CORE3.relIndex_VU_Hhat G I hBc B h1 D
  have hWn : (W.subgroupOf B.Hhat).Normal := by
    rw [hW]; exact Work.CORE3.normal_VU_subgroupOf G I hBc B h1 D
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
  have hWle : W ≤ B.Hhat := by
    rw [hW]
    exact sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat h26) (Work.CORE2A.thm26Concl_U_le_Hhat h26)
  have hDle : Dsub ≤ B.Hhat := by rw [hDsub]; exact inf_le_left
  have hnormW : B.Hhat ≤ Subgroup.normalizer (W : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact (Subgroup.normal_subgroupOf_iff hWle).mp hWn a k ha hk
    · intro ha
      have h2 : k⁻¹ * (k * a * k⁻¹) * (k⁻¹)⁻¹ ∈ W :=
        (Subgroup.normal_subgroupOf_iff hWle).mp hWn (k * a * k⁻¹) k⁻¹ ha (B.Hhat.inv_mem hk)
      have h3 : k⁻¹ * (k * a * k⁻¹) * (k⁻¹)⁻¹ = a := by group
      rwa [h3] at h2
  have h4 : 4 ≤ Work.GW2.cosetInvCount B.Hhat y := by omega
  obtain ⟨hsup, -, -⟩ := Work.CORE3.Case1bDStructure G I hBc B h1 D y hy2 hyH h4
  have htriv : W ⊓ Dsub = ⊥ := by
    rw [hW, hDsub]
    exact Work.CORE3.J4.J4DTriv (X := X) I hBc B h1 D hy2 hyH hy4 hXle hXne hXodd hinv
      hCeven hNeven hU3
  have hcard := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot
    (H := W) (K := Dsub) (le_trans hDle hnormW) (by simpa [inf_comm] using htriv)
  have hDsup : W ⊔ Dsub = B.Hhat := by rw [sup_comm]; exact hsup
  rw [hDsup] at hcard
  have hHhat : Nat.card ↥B.Hhat = 6 * Nat.card ↥W := by
    have hh := Subgroup.relIndex_mul_card (H := W) (K := B.Hhat)
    rw [inf_eq_left.mpr hWle, hWrel] at hh
    exact hh.symm
  rw [hHhat] at hcard
  have h6 : Nat.card ↥W * 6 = Nat.card ↥W * Nat.card ↥Dsub := by
    rw [mul_comm (Nat.card ↥W) 6]
    exact hcard
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h6).symm

/-- **Bender's (6)/(7) counting exclusion of `n = 6`**, in sorry-free form.

This is `Work.CORE3.CosetInvCountNeSix` with the tainted citation of `Work.CORE3.BenderSeven`
replaced by the repaired step (7) (`Work.CORE3.D23.J4U3V18s`) together with the two sorry-free
conversions `Work.CORE3.Case1bSevenLeFour` + `Work.CORE3.Case1bSevenInvInI` (the `n = 4` pinning)
and the local `cardInfConjSubOfThree` (the `|Ĥ ⊓ Ĥ^y| = 6` conclusion). -/
theorem cosetInvCount_ne_six_clean {G : Type} [Group G] [Finite G]
    (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1}) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y ≠ 6 := by
  refine Work.CORE3.cosetInvCount_ne_six_of G I hBc B h1 D h5 ?_ ?_
  · intro y hy2 hyH hbig
    exact benderSixNeSixConfig G I hBc B h1 D h5 y hy2 hyH hbig
  · intro y X hy2 hyH hXle hXne hXodd hinv hCeven hNeven s hsH hs2 hsX
    have hL1 : Work.CORE3.D23.InvolActionUniformProp :=
      Work.CORE3.D23.involActionUniformProp
    have hL3 : Work.CORE3.D23.FittingFaithfulFourProp :=
      fun G' _ _ _I _h B' _h1 _D g Y hYF hYH hV =>
        Work.CORE3.D23.FittingFaithfulFour G' _I _h B' _h1 _D g Y hYF hYH hV
    have hL4 : Work.CORE3.D23.CardUOfFittingThreeProp :=
      fun G' _ _ _I _h B' _h1 _D hF =>
        card_U_eq_three_of_card_fittingIn_eq_three (G := G') B' hF
    have hU3 : Nat.card B.U = 3 :=
      Work.CORE3.D23.J4U3V18s hL1 hL3 hL4 G I hBc B h1 D hy2 hyH X hXle hXne hXodd hinv
        hCeven hsH hs2 hsX
    have hle : Work.GW2.cosetInvCount B.Hhat y ≤ 4 :=
      Work.CORE3.Case1bSevenLeFour G I hBc B h1 D hU3 y hy2 hyH
    have hge4 : 4 ≤ Work.GW2.cosetInvCount B.Hhat y :=
      Work.CORE3.Case1bSevenInvInI G I hBc B h1 D hU3 hy2 hyH hXle hXne hXodd hinv hCeven
    have hy4 : Work.GW2.cosetInvCount B.Hhat y = 4 := le_antisymm hle hge4
    exact ⟨hU3, cardInfConjSubOfThree I hBc B h1 D hy2 hyH X hXle hXne hXodd
      hinv hCeven hNeven hU3 hy4⟩

/-- The weighted reduction `∑ (n - 3) bₙ = -3 b₀ - 2 b₁ - b₂ + b₄` for `bₙ = 0` (`n ≥ 5`);
Bender 1981 §3, (4) + (6). -/
private theorem lc_sum_range_shift_eq_of_vanishes_above {N : ℕ} (hN : 5 ≤ N) {b : ℕ → ℕ}
    (hb : ∀ n, 5 ≤ n → b n = 0) :
    ∑ n ∈ Finset.range (N + 1), ((n : ℤ) - 3) * (b n : ℤ)
      = -3 * (b 0 : ℤ) - 2 * (b 1 : ℤ) - (b 2 : ℤ) + (b 4 : ℤ) := by
  have hsub : Finset.range 5 ⊆ Finset.range (N + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hzero : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.range 5 →
      ((x : ℤ) - 3) * (b x : ℤ) = 0 := by
    intro x _ hx5
    simp only [Finset.mem_range, not_lt] at hx5
    rw [hb x hx5, Nat.cast_zero, mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  ring

/-- **Bender 1981 §3, pp. 223–224, (6)–(9)**, reproved without the `sorry`-carrying
`Work.CORE3.Case1bEightNine`.

The proof is that of `Work.CORE3.Case1bEightNine` with one change: the `(7)` conjunct is
supplied by the repaired assembly `Work.CORE3.D23.J4U3V18s` (instead of
`Work.CORE3.BenderSevenU3`), and the `n ≠ 6` input comes from `cosetInvCount_ne_six_clean`. -/
theorem case1bEightNine_of_lc (I : Work.CORE3.Case1Inputs)
    (hCount : Work.GW2.Case1bCountProp) : Work.GW2.Case1bEightNineProp := by
  intro G _ _ hFT hBc B h1 D
  classical
  have h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1} :=
    Work.CORE3.VUInvSetTrivial G I hBc B h1 D
  have hA : ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y ≤ 4 := by
    intro y hy2 hyH
    have h6 := Work.CORE3.cosetInvCount_le_six G I hBc B h1 D h5 y hy2 hyH
    have hne5 := Work.CORE3.CosetInvCountNeFive G I hBc B h1 D h5 y hy2 hyH
    have hne6 := cosetInvCount_ne_six_clean I hBc B h1 D h5 y hy2 hyH
    omega
  have hB : ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y = 4 →
      Work.CORE3.cosetPairCount B.Hhat y = 6 :=
    fun y hy hyH h4 => Work.CORE3.CosetPairCountFour G I hBc B h1 D y hy hyH h4
  have hCent : ∀ s : G, orderOf s = 2 →
      (Work.GW2.involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K :=
    fun s hs => Work.CORE3.InvolutionCentralizerCount G I hBc B h1 D s hs
  have hVsharp : ∀ s : G, s ∈ Work.GW2.pCoreIn 2 B.Hhat → orderOf s = 2 →
      (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K :=
    fun s hsV hs => Work.CORE3.CommutingInvolsVsharp G I hBc B h1 D s hsV hs
  have hOut : ∀ s : G, s ∈ B.Hhat → orderOf s = 2 → s ∉ Work.GW2.pCoreIn 2 B.Hhat →
      (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard = 3 :=
    fun s hsH hs hsV => Work.CORE3.CommutingInvolsOutsideV G I hBc B h1 D s hsH hs hsV
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact Work.CORE3.bCount_eq_zero_of_involution_bound B.Hhat hA n hn
  · have hT1 := Work.CORE3.CommutingPairTallyCosets G I hBc B h1 D hA hB
    have hT2 := Work.CORE3.CommutingPairTallyCentralizers G I hBc B h1 D hCount hCent hVsharp hOut
    have hmain : 2 * Work.GW2.bCount B.Hhat 2 + 6 * Work.GW2.bCount B.Hhat 4
        = 12 * Nat.card D.K ^ 2 := hT1.symm.trans hT2
    have hmain' : 2 * (3 * Work.GW2.bCount B.Hhat 4 + Work.GW2.bCount B.Hhat 2)
        = 12 * Nat.card D.K ^ 2 := by
      rw [show 2 * (3 * Work.GW2.bCount B.Hhat 4 + Work.GW2.bCount B.Hhat 2)
          = 2 * Work.GW2.bCount B.Hhat 2 + 6 * Work.GW2.bCount B.Hhat 4 by ring]
      exact hmain
    have h2 : 12 * Nat.card D.K ^ 2 = 2 * (6 * Nat.card D.K ^ 2) := by ring
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) (by rw [hmain', h2])
  · intro hb4
    obtain ⟨c, hc1, hc2⟩ : ∃ c : G ⧸ B.Hhat, c ≠ ((1 : G) : G ⧸ B.Hhat) ∧
        Work.GW2.cosetInvCount B.Hhat (Quotient.out c) = 4 := by
      by_contra hcon
      apply hb4
      rw [Work.GW2.bCount, Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
      rintro c ⟨hc1, hc2⟩
      exact hcon ⟨c, hc1, hc2⟩
    obtain ⟨y, hy2, hymem⟩ : ∃ y : G, orderOf y = 2 ∧
        (Quotient.out c)⁻¹ * y ∈ B.Hhat := by
      by_contra hcon
      have hempty : ({x : G | orderOf x = 2 ∧ (Quotient.out c)⁻¹ * x ∈ B.Hhat} : Set G) = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hcon ⟨x, hx.1, hx.2⟩)
      rw [Work.GW2.cosetInvCount, hempty, Set.ncard_empty] at hc2
      exact absurd hc2 (by norm_num)
    have hyH : y ∉ B.Hhat := by
      intro hyh
      have h2 : Quotient.out c = y * ((Quotient.out c)⁻¹ * y)⁻¹ := by group
      have hout : Quotient.out c ∈ B.Hhat := by
        rw [h2]
        exact B.Hhat.mul_mem hyh (B.Hhat.inv_mem hymem)
      exact Work.CORE3.quotient_out_notMem (Hh := B.Hhat) hc1 hout
    have hy4 : Work.GW2.cosetInvCount B.Hhat y = 4 := by
      rw [← hc2]
      exact (Work.CORE3.cosetInvCount_eq_of_leftCoset_eq (x := Quotient.out c) (y := y) (by
        rw [leftCoset_eq_iff]
        exact mem_leftCoset.mpr hymem)).symm
    obtain ⟨z, hz2, ⟨hh, hhH, hzy⟩, X, hXle, hXne, hXodd, hXinv, hCeven, _hNeven,
      ⟨s, hsH, hs2, hsX⟩⟩ :=
      Work.CORE3.J4.J4CosetStep (G := G) I hBc B h1 D hy2 hyH hy4
    have hzH : z ∉ B.Hhat := by
      intro hcon
      apply hyH
      have h1 : hh⁻¹ * z ∈ B.Hhat := B.Hhat.mul_mem (B.Hhat.inv_mem hhH) hcon
      rw [hzy] at h1
      simpa using h1
    have hL1 : Work.CORE3.D23.InvolActionUniformProp :=
      Work.CORE3.D23.involActionUniformProp
    have hL3 : Work.CORE3.D23.FittingFaithfulFourProp :=
      fun G' _ _ _I _h B' _h1 _D g Y hYF hYH hV =>
        Work.CORE3.D23.FittingFaithfulFour G' _I _h B' _h1 _D g Y hYF hYH hV
    have hL4 : Work.CORE3.D23.CardUOfFittingThreeProp :=
      fun G' _ _ _I _h B' _h1 _D hF =>
        card_U_eq_three_of_card_fittingIn_eq_three (G := G') B' hF
    have hU3 : Nat.card B.U = 3 :=
      Work.CORE3.D23.J4U3V18s hL1 hL3 hL4 G I hBc B h1 D hz2 hzH X hXle hXne hXodd hXinv
        hCeven hsH hs2 hsX
    refine ⟨hU3, ?_⟩
    have hKU : D.K ≤ B.U :=
      (Work.CORE2A.isHallIn_le D.hall).trans (Subgroup.map_subtype_le _)
    have hdvd : Nat.card D.K ∣ Nat.card B.U := Subgroup.card_dvd_of_le hKU
    rw [hU3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1' | h3'
    · exact absurd (Subgroup.card_eq_one.mp h1') D.ne
    · exact h3'

/-- **`Work.CORE3.J4U3V18Aux.LcFailsOfCardU`.**  In the `(1b)` configuration with `|U| ≠ 3`,
Bender's local control (clause (ii) of case (1) of Theorem 2.10) fails: some nontrivial subgroup
`Y` of `F(U)` has `N_G(Y) ⊄ Ĥ`.

Proof: suppose local control holds (`hlc`).  Then the first clause of `Case1 B` is available as
well (`hcase1i`), so the `(1b)`-analysis runs: `Case1bEightNineProp` holds
(`case1bEightNine_of_lc`, from `Case1bCountProp`), and the arithmetic of
`Work.CORE3.Case1bNumerics` gives `b₄ ≠ 0`, whence `|U| = 3`, contradicting the hypothesis. -/
theorem LcFailsOfCardU {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case1bData B)
    (hU : Nat.card B.U ≠ 3) :
    ∃ Y : Subgroup G, Y ≠ ⊥ ∧ Y ≤ Work.GW2.fittingIn B.U ∧
      ¬ (Subgroup.normalizer (Y : Set G) ≤ B.Hhat) := by
  classical
  by_contra hcon
  -- clause (ii) of case (1)
  have hlc : ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ Work.GW2.fittingIn B.U →
      Subgroup.normalizer (Y : Set G) ≤ B.Hhat := by
    intro Y hYne hYF
    by_contra hNY
    exact hcon ⟨Y, hYne, hYF, hNY⟩
  -- clause (i): `I_U(s)` is Hall in `F(U)` for `s ∈ S ∖ S₀`
  have hcase1i : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 →
      ∃ I : Subgroup G, (I : Set G) = Work.GW2.invSet B.U s ∧
        Work.GW2.IsHallIn I (Work.GW2.fittingIn B.U) := by
    intro s hsS hsS0
    have hsH : s ∈ B.Hhat := Work.CORE2A.bSetup_S_le_Hhat B hsS
    -- `S ≅ D₈`: `|S| = 8` and `S` contains the four-group `V = O₂(Ĥ)`
    obtain ⟨n, hn2, hdihn⟩ := Work.CORE3.SylowDihedral G h B
    have hn4 : n = 4 := by
      obtain ⟨e⟩ := hdihn
      have h1 : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      rw [D.S8] at h1
      omega
    have hdih4 : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup 4) := by
      rw [hn4] at hdihn
      exact hdihn
    have hs2 : orderOf s = 2 :=
      Work.CORE3.OutsideS0OrderTwo G h B 4 (by norm_num) hdih4 s hsS hsS0
    by_cases hsV : s ∈ Work.GW2.pCoreIn 2 B.Hhat
    · -- `s ∈ V` centralises `U`, so `invSet B.U s = {1}` is trivially Hall
      have hVcU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
        have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft h B
        rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]
        exact inf_le_right
      have hmem : ∀ x : G, x ∈ Work.GW2.invSet B.U s ↔ x = 1 := by
        intro x
        constructor
        · rintro ⟨hxU, hinv⟩
          have hcomm : s * x * s⁻¹ = x := by
            have hh : x * s = s * x := Subgroup.mem_centralizer_iff.mp (hVcU hsV) x hxU
            rw [← hh]
            group
          rw [hcomm] at hinv
          have hx2 : x * x = 1 := by
            have h2 : x * x = x⁻¹ * x := congrArg (· * x) hinv
            rwa [inv_mul_cancel] at h2
          have hdvd : orderOf x ∣ 2 :=
            orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
          have hodd : Odd (orderOf x) :=
            (Work.CORE2A.bSetup_U_odd B).of_dvd_nat (Subgroup.orderOf_dvd_natCard B.U hxU)
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
          · exact orderOf_eq_one_iff.mp hh
          · rw [hh] at hodd
            obtain ⟨k, hk⟩ := hodd
            omega
        · intro hx
          subst hx
          exact ⟨B.U.one_mem, by simp⟩
      refine ⟨⊥, ?_, ?_⟩
      · ext x
        constructor
        · intro hx
          exact (hmem x).mpr (by simpa using hx)
        · intro hx
          have hx1 : x = 1 := (hmem x).mp hx
          rw [hx1]
          simp
      · refine ⟨bot_le, ?_⟩
        rw [Subgroup.card_bot]
        exact Nat.coprime_one_left _
    · exact ⟨D.K, D.inv s hsH hs2 hsV, D.hall⟩
  have hcase1 : Work.GW2.Case1 B := ⟨hcase1i, hlc⟩
  -- the `(1b)` elimination
  have hCount := Work.CORE3.Case1bCount I
  obtain ⟨-, -, hIdx, hWsum, -⟩ := hCount G I.T.ft h B hcase1 D
  obtain ⟨hvan, h89b, h89c⟩ := case1bEightNine_of_lc I hCount G I.T.ft h B hcase1 D
  have hHle : B.H ≤ B.Hhat := B.H_le_Hhat
  have hrel : B.H.relIndex B.Hhat = 3 := by
    have hh := Subgroup.relIndex_mul_index hHle
    rw [hIdx] at hh
    exact Nat.mul_right_cancel
      (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := B.Hhat))) hh
  have hcardHhat : Nat.card B.Hhat = 3 * Nat.card B.H := by
    have hh := Subgroup.relIndex_mul_card B.H B.Hhat
    rw [inf_eq_left.mpr hHle] at hh
    rw [hrel] at hh
    exact hh.symm
  have hSH : Nat.card (B.S : Subgroup G) ≤ Nat.card B.H :=
    Nat.card_le_card_of_injective
      (fun s : ↥(B.S : Subgroup G) => (⟨(s : G), Work.CORE2A.bSetup_S_le_H B s.2⟩ : ↥B.H))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have hN5 : 5 ≤ Nat.card B.Hhat := by
    rw [D.S8] at hSH
    rw [hcardHhat]
    omega
  have hsum_i : ∑ n ∈ Finset.range (Nat.card B.Hhat + 1),
        ((n : ℤ) - 3) * (Work.GW2.bCount B.Hhat n : ℤ)
      = -3 * (Work.GW2.bCount B.Hhat 0 : ℤ) - 2 * (Work.GW2.bCount B.Hhat 1 : ℤ)
        - (Work.GW2.bCount B.Hhat 2 : ℤ) + (Work.GW2.bCount B.Hhat 4 : ℤ) :=
    lc_sum_range_shift_eq_of_vanishes_above hN5 hvan
  have hEqz : (6 : ℤ) * (Nat.card D.K : ℤ) + (-3 * (Work.GW2.bCount B.Hhat 0 : ℤ)
      - 2 * (Work.GW2.bCount B.Hhat 1 : ℤ) - (Work.GW2.bCount B.Hhat 2 : ℤ)
      + (Work.GW2.bCount B.Hhat 4 : ℤ)) = 0 := by
    rw [← hsum_i]
    exact hWsum
  -- `b₄ ≠ 0`: otherwise `(4)` and `(8)` force `|K| ≤ 1`, against `K ≠ ⊥`
  have hb4ne : Work.GW2.bCount B.Hhat 4 ≠ 0 := by
    intro hb4
    have hb2 : Work.GW2.bCount B.Hhat 2 = 6 * (Nat.card D.K) ^ 2 := by
      have hh := h89b
      rw [hb4, mul_zero, zero_add] at hh
      exact hh
    have hb2z : (Work.GW2.bCount B.Hhat 2 : ℤ) = 6 * (Nat.card D.K : ℤ) ^ 2 := by
      rw [hb2]; push_cast; ring
    have hb4z : (Work.GW2.bCount B.Hhat 4 : ℤ) = 0 := by rw [hb4]; norm_num
    have hb0z : (0 : ℤ) ≤ (Work.GW2.bCount B.Hhat 0 : ℤ) := by exact_mod_cast Nat.zero_le _
    have hb1z : (0 : ℤ) ≤ (Work.GW2.bCount B.Hhat 1 : ℤ) := by exact_mod_cast Nat.zero_le _
    have hle : 6 * (Nat.card D.K : ℤ) ^ 2 ≤ 6 * (Nat.card D.K : ℤ) := by
      nlinarith [hEqz, hb2z, hb4z, hb0z, hb1z]
    have hleN : 6 * (Nat.card D.K) ^ 2 ≤ 6 * Nat.card D.K := by exact_mod_cast hle
    have hkk : Nat.card D.K * Nat.card D.K ≤ Nat.card D.K := by
      have h2 : 6 * (Nat.card D.K * Nat.card D.K) ≤ 6 * Nat.card D.K := by
        simpa [pow_two] using hleN
      exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
    have hk1 : Nat.card D.K ≤ 1 := by
      by_contra hk
      have hk2 : 2 ≤ Nat.card D.K := by omega
      have h2 : 2 * Nat.card D.K ≤ Nat.card D.K * Nat.card D.K := Nat.mul_le_mul_right _ hk2
      omega
    have hk1' : Nat.card D.K = 1 := by
      have : 0 < Nat.card D.K := Nat.card_pos
      omega
    exact D.ne ((Subgroup.card_eq_one).mp hk1')
  exact hU (h89c hb4ne).1

end Work.CORE3.J4U3V18Aux
