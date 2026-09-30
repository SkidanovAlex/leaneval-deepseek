import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts0
import Submission.Work.BridgeSquare.SlabBuild.Infra

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.BridgeSquare.SlabBuild

open Convexity
open Work.Subdivision
open Work.MbarHomology
open Work.BridgeSquare.WallCollar

noncomputable section



/-! ### cusp 0, cell 16 (root face 58) -/

/-- The eight `(f,u)`-chains of the root face of cell `16`. -/
def LP_0_16 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨196⟩, ⟨843⟩), by decide +kernel⟩,
  ⟨(⟨196⟩, ⟨855⟩), by decide +kernel⟩,
  ⟨(⟨260⟩, ⟨780⟩), by decide +kernel⟩,
  ⟨(⟨260⟩, ⟨795⟩), by decide +kernel⟩,
  ⟨(⟨332⟩, ⟨795⟩), by decide +kernel⟩,
  ⟨(⟨332⟩, ⟨855⟩), by decide +kernel⟩,
  ⟨(⟨336⟩, ⟨780⟩), by decide +kernel⟩,
  ⟨(⟨336⟩, ⟨843⟩), by decide +kernel⟩]

theorem LP_0_16_inj : Function.Injective LP_0_16 := by decide +kernel

theorem LP_0_16_surj : Function.Surjective LP_0_16 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨196⟩, ⟨260⟩, ⟨332⟩, ⟨336⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨196⟩ : QbarCW.Cell) = {⟨843⟩, ⟨855⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨260⟩ : QbarCW.Cell) = {⟨780⟩, ⟨795⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨332⟩ : QbarCW.Cell) = {⟨795⟩, ⟨855⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨336⟩ : QbarCW.Cell) = {⟨780⟩, ⟨843⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_0_24 : cChain 0 (slabV 0 (tauV0 24)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_813_200

theorem chC_0_25 : cChain 0 (slabV 0 (tauV0 25)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_828_200

theorem chC_0_26 : cChain 0 (slabV 0 (tauV0 26)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_744_264

theorem chC_0_27 : cChain 0 (slabV 0 (tauV0 27)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_762_264

theorem chC_0_28 : cChain 0 (slabV 0 (tauV0 28)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_762_380

theorem chC_0_29 : cChain 0 (slabV 0 (tauV0 29)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_828_380

theorem chC_0_30 : cChain 0 (slabV 0 (tauV0 30)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_744_384

theorem chC_0_31 : cChain 0 (slabV 0 (tauV0 31)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_813_384

/-- **Wall leaf (cusp 0, cell 16)**: the 8 wall triangles of cell `16` give its `Ψ_M`-image. -/
theorem wallCell_0_16 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx0 => cellV0 j = 16), coefV0 j • cChain 0 (slabV 0 (tauV0 j)))
      = planeCycleVec 0 0 (16 : Fin 192) • (PsiM.f 2) (Pi.single (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx0 => cellV0 j = 16) = {24, 25, 26, 27, 28, 29, 30, 31} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_0_16) LP_0_16_inj LP_0_16_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_0_24, chC_0_25, chC_0_26, chC_0_27, chC_0_28, chC_0_29, chC_0_30, chC_0_31]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 0).1.1.idx) * qInc (LP_0_16 0).1.1.idx (LP_0_16 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 1).1.1.idx) * qInc (LP_0_16 1).1.1.idx (LP_0_16 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 2).1.1.idx) * qInc (LP_0_16 2).1.1.idx (LP_0_16 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 3).1.1.idx) * qInc (LP_0_16 3).1.1.idx (LP_0_16 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 4).1.1.idx) * qInc (LP_0_16 4).1.1.idx (LP_0_16 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 5).1.1.idx) * qInc (LP_0_16 5).1.1.idx (LP_0_16 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 6).1.1.idx) * qInc (LP_0_16 6).1.1.idx (LP_0_16 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 7).1.1.idx) * qInc (LP_0_16 7).1.1.idx (LP_0_16 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 0 0 (16 : Fin 192) = 1 := by decide +kernel
  have a24 : coefV0 24 = -1 := by decide +kernel
  have a25 : coefV0 25 = 1 := by decide +kernel
  have a26 : coefV0 26 = 1 := by decide +kernel
  have a27 : coefV0 27 = -1 := by decide +kernel
  have a28 : coefV0 28 = 1 := by decide +kernel
  have a29 : coefV0 29 = -1 := by decide +kernel
  have a30 : coefV0 30 = -1 := by decide +kernel
  have a31 : coefV0 31 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a24, a25, a26, a27, a28, a29, a30, a31]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 0, cell 22 (root face 65) -/

/-- The eight `(f,u)`-chains of the root face of cell `22`. -/
def LP_0_22 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨228⟩, ⟨708⟩), by decide +kernel⟩,
  ⟨(⟨228⟩, ⟨723⟩), by decide +kernel⟩,
  ⟨(⟨292⟩, ⟨633⟩), by decide +kernel⟩,
  ⟨(⟨292⟩, ⟨651⟩), by decide +kernel⟩,
  ⟨(⟨356⟩, ⟨651⟩), by decide +kernel⟩,
  ⟨(⟨356⟩, ⟨723⟩), by decide +kernel⟩,
  ⟨(⟨360⟩, ⟨633⟩), by decide +kernel⟩,
  ⟨(⟨360⟩, ⟨708⟩), by decide +kernel⟩]

theorem LP_0_22_inj : Function.Injective LP_0_22 := by decide +kernel

theorem LP_0_22_surj : Function.Surjective LP_0_22 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨228⟩, ⟨292⟩, ⟨356⟩, ⟨360⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨228⟩ : QbarCW.Cell) = {⟨708⟩, ⟨723⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨292⟩ : QbarCW.Cell) = {⟨633⟩, ⟨651⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨356⟩ : QbarCW.Cell) = {⟨651⟩, ⟨723⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨360⟩ : QbarCW.Cell) = {⟨633⟩, ⟨708⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_0_16 : cChain 0 (slabV 0 (tauV0 16)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_672_232

theorem chC_0_17 : cChain 0 (slabV 0 (tauV0 17)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_690_232

theorem chC_0_18 : cChain 0 (slabV 0 (tauV0 18)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_591_296

theorem chC_0_19 : cChain 0 (slabV 0 (tauV0 19)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_612_296

theorem chC_0_20 : cChain 0 (slabV 0 (tauV0 20)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_612_404

theorem chC_0_21 : cChain 0 (slabV 0 (tauV0 21)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_690_404

theorem chC_0_22 : cChain 0 (slabV 0 (tauV0 22)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_591_408

theorem chC_0_23 : cChain 0 (slabV 0 (tauV0 23)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_672_408

/-- **Wall leaf (cusp 0, cell 22)**: the 8 wall triangles of cell `22` give its `Ψ_M`-image. -/
theorem wallCell_0_22 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx0 => cellV0 j = 22), coefV0 j • cChain 0 (slabV 0 (tauV0 j)))
      = planeCycleVec 0 0 (22 : Fin 192) • (PsiM.f 2) (Pi.single (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx0 => cellV0 j = 22) = {16, 17, 18, 19, 20, 21, 22, 23} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_0_22) LP_0_22_inj LP_0_22_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_0_16, chC_0_17, chC_0_18, chC_0_19, chC_0_20, chC_0_21, chC_0_22, chC_0_23]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 0).1.1.idx) * qInc (LP_0_22 0).1.1.idx (LP_0_22 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 1).1.1.idx) * qInc (LP_0_22 1).1.1.idx (LP_0_22 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 2).1.1.idx) * qInc (LP_0_22 2).1.1.idx (LP_0_22 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 3).1.1.idx) * qInc (LP_0_22 3).1.1.idx (LP_0_22 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 4).1.1.idx) * qInc (LP_0_22 4).1.1.idx (LP_0_22 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 5).1.1.idx) * qInc (LP_0_22 5).1.1.idx (LP_0_22 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 6).1.1.idx) * qInc (LP_0_22 6).1.1.idx (LP_0_22 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 7).1.1.idx) * qInc (LP_0_22 7).1.1.idx (LP_0_22 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 0 0 (22 : Fin 192) = -1 := by decide +kernel
  have a16 : coefV0 16 = 1 := by decide +kernel
  have a17 : coefV0 17 = -1 := by decide +kernel
  have a18 : coefV0 18 = -1 := by decide +kernel
  have a19 : coefV0 19 = 1 := by decide +kernel
  have a20 : coefV0 20 = -1 := by decide +kernel
  have a21 : coefV0 21 = 1 := by decide +kernel
  have a22 : coefV0 22 = 1 := by decide +kernel
  have a23 : coefV0 23 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a16, a17, a18, a19, a20, a21, a22, a23]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 0, cell 152 (root face 58) -/

/-- The eight `(f,u)`-chains of the root face of cell `152`. -/
def LP_0_152 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨196⟩, ⟨843⟩), by decide +kernel⟩,
  ⟨(⟨196⟩, ⟨855⟩), by decide +kernel⟩,
  ⟨(⟨260⟩, ⟨780⟩), by decide +kernel⟩,
  ⟨(⟨260⟩, ⟨795⟩), by decide +kernel⟩,
  ⟨(⟨332⟩, ⟨795⟩), by decide +kernel⟩,
  ⟨(⟨332⟩, ⟨855⟩), by decide +kernel⟩,
  ⟨(⟨336⟩, ⟨780⟩), by decide +kernel⟩,
  ⟨(⟨336⟩, ⟨843⟩), by decide +kernel⟩]

theorem LP_0_152_inj : Function.Injective LP_0_152 := by decide +kernel

theorem LP_0_152_surj : Function.Surjective LP_0_152 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨196⟩, ⟨260⟩, ⟨332⟩, ⟨336⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨196⟩ : QbarCW.Cell) = {⟨843⟩, ⟨855⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨260⟩ : QbarCW.Cell) = {⟨780⟩, ⟨795⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨332⟩ : QbarCW.Cell) = {⟨795⟩, ⟨855⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨336⟩ : QbarCW.Cell) = {⟨780⟩, ⟨843⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_0_0 : cChain 0 (slabV 0 (tauV0 0)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_196
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_843_196

theorem chC_0_1 : cChain 0 (slabV 0 (tauV0 1)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_196
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_855_196

theorem chC_0_2 : cChain 0 (slabV 0 (tauV0 2)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_260
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_780_260

theorem chC_0_3 : cChain 0 (slabV 0 (tauV0 3)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_260
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_795_260

theorem chC_0_4 : cChain 0 (slabV 0 (tauV0 4)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_332
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_795_332

theorem chC_0_5 : cChain 0 (slabV 0 (tauV0 5)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_332
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_855_332

theorem chC_0_6 : cChain 0 (slabV 0 (tauV0 6)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_336
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_780_336

theorem chC_0_7 : cChain 0 (slabV 0 (tauV0 7)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_336
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_843_336

/-- **Wall leaf (cusp 0, cell 152)**: the 8 wall triangles of cell `152` give its `Ψ_M`-image. -/
theorem wallCell_0_152 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx0 => cellV0 j = 152), coefV0 j • cChain 0 (slabV 0 (tauV0 j)))
      = planeCycleVec 0 0 (152 : Fin 192) • (PsiM.f 2) (Pi.single (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx0 => cellV0 j = 152) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_0_152) LP_0_152_inj LP_0_152_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_0_0, chC_0_1, chC_0_2, chC_0_3, chC_0_4, chC_0_5, chC_0_6, chC_0_7]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 0).1.1.idx) * qInc (LP_0_152 0).1.1.idx (LP_0_152 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 1).1.1.idx) * qInc (LP_0_152 1).1.1.idx (LP_0_152 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 2).1.1.idx) * qInc (LP_0_152 2).1.1.idx (LP_0_152 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 3).1.1.idx) * qInc (LP_0_152 3).1.1.idx (LP_0_152 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 4).1.1.idx) * qInc (LP_0_152 4).1.1.idx (LP_0_152 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 5).1.1.idx) * qInc (LP_0_152 5).1.1.idx (LP_0_152 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 6).1.1.idx) * qInc (LP_0_152 6).1.1.idx (LP_0_152 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 7).1.1.idx) * qInc (LP_0_152 7).1.1.idx (LP_0_152 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 0 0 (152 : Fin 192) = 1 := by decide +kernel
  have a0 : coefV0 0 = -1 := by decide +kernel
  have a1 : coefV0 1 = 1 := by decide +kernel
  have a2 : coefV0 2 = 1 := by decide +kernel
  have a3 : coefV0 3 = -1 := by decide +kernel
  have a4 : coefV0 4 = 1 := by decide +kernel
  have a5 : coefV0 5 = -1 := by decide +kernel
  have a6 : coefV0 6 = -1 := by decide +kernel
  have a7 : coefV0 7 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a0, a1, a2, a3, a4, a5, a6, a7]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 0, cell 158 (root face 65) -/

/-- The eight `(f,u)`-chains of the root face of cell `158`. -/
def LP_0_158 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨228⟩, ⟨708⟩), by decide +kernel⟩,
  ⟨(⟨228⟩, ⟨723⟩), by decide +kernel⟩,
  ⟨(⟨292⟩, ⟨633⟩), by decide +kernel⟩,
  ⟨(⟨292⟩, ⟨651⟩), by decide +kernel⟩,
  ⟨(⟨356⟩, ⟨651⟩), by decide +kernel⟩,
  ⟨(⟨356⟩, ⟨723⟩), by decide +kernel⟩,
  ⟨(⟨360⟩, ⟨633⟩), by decide +kernel⟩,
  ⟨(⟨360⟩, ⟨708⟩), by decide +kernel⟩]

theorem LP_0_158_inj : Function.Injective LP_0_158 := by decide +kernel

theorem LP_0_158_surj : Function.Surjective LP_0_158 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨228⟩, ⟨292⟩, ⟨356⟩, ⟨360⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨228⟩ : QbarCW.Cell) = {⟨708⟩, ⟨723⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨292⟩ : QbarCW.Cell) = {⟨633⟩, ⟨651⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨356⟩ : QbarCW.Cell) = {⟨651⟩, ⟨723⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨360⟩ : QbarCW.Cell) = {⟨633⟩, ⟨708⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_0_8 : cChain 0 (slabV 0 (tauV0 8)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_228
      = mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_1_708_228

theorem chC_0_9 : cChain 0 (slabV 0 (tauV0 9)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_228
      = mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_1_723_228

theorem chC_0_10 : cChain 0 (slabV 0 (tauV0 10)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_292
      = mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_1_633_292

theorem chC_0_11 : cChain 0 (slabV 0 (tauV0 11)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292
      = mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_1_651_292

theorem chC_0_12 : cChain 0 (slabV 0 (tauV0 12)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356
      = mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_1_651_356

theorem chC_0_13 : cChain 0 (slabV 0 (tauV0 13)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356
      = mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_1_723_356

theorem chC_0_14 : cChain 0 (slabV 0 (tauV0 14)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360
      = mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_1_633_360

theorem chC_0_15 : cChain 0 (slabV 0 (tauV0 15)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360
      = mkSimplex (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_158 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_1_708_360

/-- **Wall leaf (cusp 0, cell 158)**: the 8 wall triangles of cell `158` give its `Ψ_M`-image. -/
theorem wallCell_0_158 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx0 => cellV0 j = 158), coefV0 j • cChain 0 (slabV 0 (tauV0 j)))
      = planeCycleVec 0 0 (158 : Fin 192) • (PsiM.f 2) (Pi.single (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx0 => cellV0 j = 158) = {8, 9, 10, 11, 12, 13, 14, 15} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_0_158) LP_0_158_inj LP_0_158_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_0_8, chC_0_9, chC_0_10, chC_0_11, chC_0_12, chC_0_13, chC_0_14, chC_0_15]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_158 0).1.1.idx) * qInc (LP_0_158 0).1.1.idx (LP_0_158 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_158 1).1.1.idx) * qInc (LP_0_158 1).1.1.idx (LP_0_158 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_158 2).1.1.idx) * qInc (LP_0_158 2).1.1.idx (LP_0_158 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_158 3).1.1.idx) * qInc (LP_0_158 3).1.1.idx (LP_0_158 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_158 4).1.1.idx) * qInc (LP_0_158 4).1.1.idx (LP_0_158 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_158 5).1.1.idx) * qInc (LP_0_158 5).1.1.idx (LP_0_158 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_158 6).1.1.idx) * qInc (LP_0_158 6).1.1.idx (LP_0_158 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_158 7).1.1.idx) * qInc (LP_0_158 7).1.1.idx (LP_0_158 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 0 0 (158 : Fin 192) = -1 := by decide +kernel
  have a8 : coefV0 8 = 1 := by decide +kernel
  have a9 : coefV0 9 = -1 := by decide +kernel
  have a10 : coefV0 10 = -1 := by decide +kernel
  have a11 : coefV0 11 = 1 := by decide +kernel
  have a12 : coefV0 12 = -1 := by decide +kernel
  have a13 : coefV0 13 = 1 := by decide +kernel
  have a14 : coefV0 14 = 1 := by decide +kernel
  have a15 : coefV0 15 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a8, a9, a10, a11, a12, a13, a14, a15]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### Assembly for cusp 0 -/

/-- **The wall identification for cusp 0** (untranslated triangles). -/
theorem wallPsi_0 :
    (∑ j : Idx0, coefV0 j • cChain 0 (slabV 0 (tauV0 j))) = (PsiM.f 2) (planeCycleVec 0 0) := by
  have hexp : (planeCycleVec 0 0 : Fin 192 → ℤ)
      = ∑ e ∈ ({16, 22, 152, 158} : Finset (Fin 192)), planeCycleVec 0 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ) := by
    funext i; rw [Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]; revert i; decide +kernel
  have hR : (PsiM.f 2) (planeCycleVec 0 0)
      = ∑ e ∈ ({16, 22, 152, 158} : Finset (Fin 192)), planeCycleVec 0 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
    calc (PsiM.f 2) (planeCycleVec 0 0)
        = (PsiM.f 2) (∑ e ∈ ({16, 22, 152, 158} : Finset (Fin 192)), planeCycleVec 0 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          congrArg (PsiM.f 2) hexp
      _ = ∑ e ∈ ({16, 22, 152, 158} : Finset (Fin 192)), (PsiM.f 2) (planeCycleVec 0 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          map_sum _ _ _
      _ = ∑ e ∈ ({16, 22, 152, 158} : Finset (Fin 192)), planeCycleVec 0 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
          Finset.sum_congr rfl fun e _ => map_zsmul _ _ _
  rw [hR, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := ({16, 22, 152, 158} : Finset (Fin 192))) (g := cellV0)
    (fun j _ => by revert j; decide +kernel)]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact wallCell_0_16
  · exact wallCell_0_22
  · exact wallCell_0_152
  · exact wallCell_0_158

theorem lamV_mem0 (j : Idx0) : slabL 0 (lamV0 j) ∈ Work.Cusp.lattice 0 := by
  have hk1 : Work.Cusp.kv 0 1 ∈ Work.Cusp.lattice 0 := AddSubgroup.subset_closure (Set.mem_range_self 1)
  have hk2 : Work.Cusp.kv 0 2 ∈ Work.Cusp.lattice 0 := AddSubgroup.subset_closure (Set.mem_range_self 2)
  have h : slabL 0 (lamV0 j) ∈ ({0, -Work.Cusp.kv 0 2, -Work.Cusp.kv 0 1, -Work.Cusp.kv 0 1 - Work.Cusp.kv 0 2} : Set CuspE3) := by
    fin_cases j <;> simp [lamV0, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3] <;> abel_nf <;> simp
  rcases h with h | h | h | h <;> rw [h]
  · exact zero_mem _
  · exact neg_mem hk2
  · exact neg_mem hk1
  · exact sub_mem (neg_mem hk1) hk2

/-- **The wall chain of cusp 0 realises `Ψ_M(planeCycleVec 0 0)`** (the `W` of `wall_collar 0`, `s = 1`). -/
theorem wall_slab0 : slabChain 0 2 (wallChain0 : AffC 2) = (PsiM.f 2) (planeCycleVec 0 0) := by
  rw [← wallPsi_0, wallChain0, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, slabChain_single_one]
  have h1 : slabV 0 (fun k => tauV0 j k + lamV0 j) = fun k => slabV 0 (tauV0 j) k + slabL 0 (lamV0 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 0 (slabV 0 (tauV0 j)) (slabL 0 (lamV0 j)) (lamV_mem0 j)]

end

end Work.BridgeSquare.SlabBuild
