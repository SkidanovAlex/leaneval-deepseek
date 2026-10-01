import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts4
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p1
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p2
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p3_p1

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



theorem LP_4_43_surj : Function.Surjective LP_4_43 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨303⟩, ⟨399⟩, ⟨466⟩, ⟨474⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨303⟩ : QbarCW.Cell) = {⟨579⟩, ⟨614⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨399⟩ : QbarCW.Cell) = {⟨579⟩, ⟨617⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨466⟩ : QbarCW.Cell) = {⟨608⟩, ⟨614⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨474⟩ : QbarCW.Cell) = {⟨608⟩, ⟨617⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_88 : cChain 4 (slabV 4 (tauV4 88)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_33_839_202

theorem chC_4_89 : cChain 4 (slabV 4 (tauV4 89)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_33_845_202

theorem chC_4_90 : cChain 4 (slabV 4 (tauV4 90)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_33_839_322

theorem chC_4_91 : cChain 4 (slabV 4 (tauV4 91)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_33_848_322

theorem chC_4_92 : cChain 4 (slabV 4 (tauV4 92)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_33_705_423

theorem chC_4_93 : cChain 4 (slabV 4 (tauV4 93)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_33_845_423

theorem chC_4_94 : cChain 4 (slabV 4 (tauV4 94)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_33_705_431

theorem chC_4_95 : cChain 4 (slabV 4 (tauV4 95)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_33_848_431

/-- **Wall leaf (cusp 4, cell 43)**: the 8 wall triangles of cell `43` give its `Ψ_M`-image. -/
theorem wallCell_4_43 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 43), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (43 : Fin 192) • (PsiM.f 2) (Pi.single (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 43) = {88, 89, 90, 91, 92, 93, 94, 95} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_43) LP_4_43_inj LP_4_43_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_88, chC_4_89, chC_4_90, chC_4_91, chC_4_92, chC_4_93, chC_4_94, chC_4_95]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 0).1.1.idx) * qInc (LP_4_43 0).1.1.idx (LP_4_43 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 1).1.1.idx) * qInc (LP_4_43 1).1.1.idx (LP_4_43 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 2).1.1.idx) * qInc (LP_4_43 2).1.1.idx (LP_4_43 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 3).1.1.idx) * qInc (LP_4_43 3).1.1.idx (LP_4_43 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 4).1.1.idx) * qInc (LP_4_43 4).1.1.idx (LP_4_43 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 5).1.1.idx) * qInc (LP_4_43 5).1.1.idx (LP_4_43 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 6).1.1.idx) * qInc (LP_4_43 6).1.1.idx (LP_4_43 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 7).1.1.idx) * qInc (LP_4_43 7).1.1.idx (LP_4_43 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 4 0 (43 : Fin 192) = 1 := by decide +kernel
  have a88 : coefV4 88 = -1 := by decide +kernel
  have a89 : coefV4 89 = 1 := by decide +kernel
  have a90 : coefV4 90 = 1 := by decide +kernel
  have a91 : coefV4 91 = -1 := by decide +kernel
  have a92 : coefV4 92 = 1 := by decide +kernel
  have a93 : coefV4 93 = -1 := by decide +kernel
  have a94 : coefV4 94 = -1 := by decide +kernel
  have a95 : coefV4 95 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a88, a89, a90, a91, a92, a93, a94, a95]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 44 (root face 105) -/

/-- The eight `(f,u)`-chains of the root face of cell `44`. -/
def LP_4_44 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨270⟩, ⟨734⟩), by decide +kernel⟩,
  ⟨(⟨270⟩, ⟨746⟩), by decide +kernel⟩,
  ⟨(⟨374⟩, ⟨734⟩), by decide +kernel⟩,
  ⟨(⟨374⟩, ⟨749⟩), by decide +kernel⟩,
  ⟨(⟨471⟩, ⟨588⟩), by decide +kernel⟩,
  ⟨(⟨471⟩, ⟨746⟩), by decide +kernel⟩,
  ⟨(⟨479⟩, ⟨588⟩), by decide +kernel⟩,
  ⟨(⟨479⟩, ⟨749⟩), by decide +kernel⟩]

theorem LP_4_44_inj : Function.Injective LP_4_44 := by decide +kernel

theorem LP_4_44_surj : Function.Surjective LP_4_44 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨270⟩, ⟨374⟩, ⟨471⟩, ⟨479⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨270⟩ : QbarCW.Cell) = {⟨734⟩, ⟨746⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨374⟩ : QbarCW.Cell) = {⟨734⟩, ⟨749⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨471⟩ : QbarCW.Cell) = {⟨588⟩, ⟨746⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨479⟩ : QbarCW.Cell) = {⟨588⟩, ⟨749⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_112 : cChain 4 (slabV 4 (tauV4 112)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_40_702_235

theorem chC_4_113 : cChain 4 (slabV 4 (tauV4 113)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_40_725_235

theorem chC_4_114 : cChain 4 (slabV 4 (tauV4 114)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_40_702_347

theorem chC_4_115 : cChain 4 (slabV 4 (tauV4 115)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_40_728_347

theorem chC_4_116 : cChain 4 (slabV 4 (tauV4 116)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_40_719_418

theorem chC_4_117 : cChain 4 (slabV 4 (tauV4 117)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_40_725_418

theorem chC_4_118 : cChain 4 (slabV 4 (tauV4 118)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_40_719_426

theorem chC_4_119 : cChain 4 (slabV 4 (tauV4 119)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_40_728_426

/-- **Wall leaf (cusp 4, cell 44)**: the 8 wall triangles of cell `44` give its `Ψ_M`-image. -/
theorem wallCell_4_44 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 44), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (44 : Fin 192) • (PsiM.f 2) (Pi.single (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 44) = {112, 113, 114, 115, 116, 117, 118, 119} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_44) LP_4_44_inj LP_4_44_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_112, chC_4_113, chC_4_114, chC_4_115, chC_4_116, chC_4_117, chC_4_118, chC_4_119]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 0).1.1.idx) * qInc (LP_4_44 0).1.1.idx (LP_4_44 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 1).1.1.idx) * qInc (LP_4_44 1).1.1.idx (LP_4_44 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 2).1.1.idx) * qInc (LP_4_44 2).1.1.idx (LP_4_44 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 3).1.1.idx) * qInc (LP_4_44 3).1.1.idx (LP_4_44 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 4).1.1.idx) * qInc (LP_4_44 4).1.1.idx (LP_4_44 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 5).1.1.idx) * qInc (LP_4_44 5).1.1.idx (LP_4_44 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 6).1.1.idx) * qInc (LP_4_44 6).1.1.idx (LP_4_44 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 7).1.1.idx) * qInc (LP_4_44 7).1.1.idx (LP_4_44 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (44 : Fin 192) = -1 := by decide +kernel
  have a112 : coefV4 112 = -1 := by decide +kernel
  have a113 : coefV4 113 = 1 := by decide +kernel
  have a114 : coefV4 114 = 1 := by decide +kernel
  have a115 : coefV4 115 = -1 := by decide +kernel
  have a116 : coefV4 116 = 1 := by decide +kernel
  have a117 : coefV4 117 = -1 := by decide +kernel
  have a118 : coefV4 118 = -1 := by decide +kernel
  have a119 : coefV4 119 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a112, a113, a114, a115, a116, a117, a118, a119]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 45 (root face 106) -/

/-- The eight `(f,u)`-chains of the root face of cell `45`. -/
def LP_4_45 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨271⟩, ⟨735⟩), by decide +kernel⟩,
  ⟨(⟨271⟩, ⟨764⟩), by decide +kernel⟩,
  ⟨(⟨375⟩, ⟨735⟩), by decide +kernel⟩,
  ⟨(⟨375⟩, ⟨767⟩), by decide +kernel⟩,
  ⟨(⟨467⟩, ⟨609⟩), by decide +kernel⟩,
  ⟨(⟨467⟩, ⟨764⟩), by decide +kernel⟩,
  ⟨(⟨475⟩, ⟨609⟩), by decide +kernel⟩,
  ⟨(⟨475⟩, ⟨767⟩), by decide +kernel⟩]

theorem LP_4_45_inj : Function.Injective LP_4_45 := by decide +kernel


end

end Work.BridgeSquare.SlabBuild
