import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts4
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p1

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



theorem chC_4_53 : cChain 4 (slabV 4 (tauV4 53)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_455
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_24_815_455

theorem chC_4_54 : cChain 4 (slabV 4 (tauV4 54)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_24_669_463

theorem chC_4_55 : cChain 4 (slabV 4 (tauV4 55)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_24_818_463

/-- **Wall leaf (cusp 4, cell 31)**: the 8 wall triangles of cell `31` give its `Ψ_M`-image. -/
theorem wallCell_4_31 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 31), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (31 : Fin 192) • (PsiM.f 2) (Pi.single (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 31) = {48, 49, 50, 51, 52, 53, 54, 55} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_31) LP_4_31_inj LP_4_31_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_48, chC_4_49, chC_4_50, chC_4_51, chC_4_52, chC_4_53, chC_4_54, chC_4_55]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 0).1.1.idx) * qInc (LP_4_31 0).1.1.idx (LP_4_31 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 1).1.1.idx) * qInc (LP_4_31 1).1.1.idx (LP_4_31 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 2).1.1.idx) * qInc (LP_4_31 2).1.1.idx (LP_4_31 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 3).1.1.idx) * qInc (LP_4_31 3).1.1.idx (LP_4_31 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 4).1.1.idx) * qInc (LP_4_31 4).1.1.idx (LP_4_31 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 5).1.1.idx) * qInc (LP_4_31 5).1.1.idx (LP_4_31 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 6).1.1.idx) * qInc (LP_4_31 6).1.1.idx (LP_4_31 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 7).1.1.idx) * qInc (LP_4_31 7).1.1.idx (LP_4_31 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 4 0 (31 : Fin 192) = -1 := by decide +kernel
  have a48 : coefV4 48 = 1 := by decide +kernel
  have a49 : coefV4 49 = -1 := by decide +kernel
  have a50 : coefV4 50 = -1 := by decide +kernel
  have a51 : coefV4 51 = 1 := by decide +kernel
  have a52 : coefV4 52 = -1 := by decide +kernel
  have a53 : coefV4 53 = 1 := by decide +kernel
  have a54 : coefV4 54 = 1 := by decide +kernel
  have a55 : coefV4 55 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a48, a49, a50, a51, a52, a53, a54, a55]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 32 (root face 91) -/

/-- The eight `(f,u)`-chains of the root face of cell `32`. -/
def LP_4_32 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨266⟩, ⟨773⟩), by decide +kernel⟩,
  ⟨(⟨266⟩, ⟨782⟩), by decide +kernel⟩,
  ⟨(⟨326⟩, ⟨773⟩), by decide +kernel⟩,
  ⟨(⟨326⟩, ⟨785⟩), by decide +kernel⟩,
  ⟨(⟨439⟩, ⟨630⟩), by decide +kernel⟩,
  ⟨(⟨439⟩, ⟨782⟩), by decide +kernel⟩,
  ⟨(⟨447⟩, ⟨630⟩), by decide +kernel⟩,
  ⟨(⟨447⟩, ⟨785⟩), by decide +kernel⟩]

theorem LP_4_32_inj : Function.Injective LP_4_32 := by decide +kernel

theorem LP_4_32_surj : Function.Surjective LP_4_32 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨266⟩, ⟨326⟩, ⟨439⟩, ⟨447⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨266⟩ : QbarCW.Cell) = {⟨773⟩, ⟨782⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨326⟩ : QbarCW.Cell) = {⟨773⟩, ⟨785⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨439⟩ : QbarCW.Cell) = {⟨630⟩, ⟨782⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨447⟩ : QbarCW.Cell) = {⟨630⟩, ⟨785⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_80 : cChain 4 (slabV 4 (tauV4 80)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_31_663_239

theorem chC_4_81 : cChain 4 (slabV 4 (tauV4 81)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_31_692_239

theorem chC_4_82 : cChain 4 (slabV 4 (tauV4 82)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_31_663_395

theorem chC_4_83 : cChain 4 (slabV 4 (tauV4 83)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_31_695_395

theorem chC_4_84 : cChain 4 (slabV 4 (tauV4 84)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_31_686_450

theorem chC_4_85 : cChain 4 (slabV 4 (tauV4 85)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_31_692_450

theorem chC_4_86 : cChain 4 (slabV 4 (tauV4 86)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_31_686_458

theorem chC_4_87 : cChain 4 (slabV 4 (tauV4 87)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_31_695_458

/-- **Wall leaf (cusp 4, cell 32)**: the 8 wall triangles of cell `32` give its `Ψ_M`-image. -/
theorem wallCell_4_32 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 32), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (32 : Fin 192) • (PsiM.f 2) (Pi.single (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 32) = {80, 81, 82, 83, 84, 85, 86, 87} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_32) LP_4_32_inj LP_4_32_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_80, chC_4_81, chC_4_82, chC_4_83, chC_4_84, chC_4_85, chC_4_86, chC_4_87]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 0).1.1.idx) * qInc (LP_4_32 0).1.1.idx (LP_4_32 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 1).1.1.idx) * qInc (LP_4_32 1).1.1.idx (LP_4_32 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 2).1.1.idx) * qInc (LP_4_32 2).1.1.idx (LP_4_32 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 3).1.1.idx) * qInc (LP_4_32 3).1.1.idx (LP_4_32 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 4).1.1.idx) * qInc (LP_4_32 4).1.1.idx (LP_4_32 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 5).1.1.idx) * qInc (LP_4_32 5).1.1.idx (LP_4_32 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 6).1.1.idx) * qInc (LP_4_32 6).1.1.idx (LP_4_32 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 7).1.1.idx) * qInc (LP_4_32 7).1.1.idx (LP_4_32 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (32 : Fin 192) = 1 := by decide +kernel
  have a80 : coefV4 80 = 1 := by decide +kernel
  have a81 : coefV4 81 = -1 := by decide +kernel
  have a82 : coefV4 82 = -1 := by decide +kernel
  have a83 : coefV4 83 = 1 := by decide +kernel
  have a84 : coefV4 84 = -1 := by decide +kernel
  have a85 : coefV4 85 = 1 := by decide +kernel
  have a86 : coefV4 86 = 1 := by decide +kernel
  have a87 : coefV4 87 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a80, a81, a82, a83, a84, a85, a86, a87]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 33 (root face 92) -/

/-- The eight `(f,u)`-chains of the root face of cell `33`. -/
def LP_4_33 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨267⟩, ⟨774⟩), by decide +kernel⟩,
  ⟨(⟨267⟩, ⟨797⟩), by decide +kernel⟩,
  ⟨(⟨327⟩, ⟨774⟩), by decide +kernel⟩,
  ⟨(⟨327⟩, ⟨800⟩), by decide +kernel⟩,
  ⟨(⟨435⟩, ⟨648⟩), by decide +kernel⟩,
  ⟨(⟨435⟩, ⟨797⟩), by decide +kernel⟩,
  ⟨(⟨443⟩, ⟨648⟩), by decide +kernel⟩,
  ⟨(⟨443⟩, ⟨800⟩), by decide +kernel⟩]

theorem LP_4_33_inj : Function.Injective LP_4_33 := by decide +kernel

theorem LP_4_33_surj : Function.Surjective LP_4_33 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨267⟩, ⟨327⟩, ⟨435⟩, ⟨443⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨267⟩ : QbarCW.Cell) = {⟨774⟩, ⟨797⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨327⟩ : QbarCW.Cell) = {⟨774⟩, ⟨800⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨435⟩ : QbarCW.Cell) = {⟨648⟩, ⟨797⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨443⟩ : QbarCW.Cell) = {⟨648⟩, ⟨800⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_24 : cChain 4 (slabV 4 (tauV4 24)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_20_662_238

theorem chC_4_25 : cChain 4 (slabV 4 (tauV4 25)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_20_674_238

theorem chC_4_26 : cChain 4 (slabV 4 (tauV4 26)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_20_662_394

theorem chC_4_27 : cChain 4 (slabV 4 (tauV4 27)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_20_677_394

theorem chC_4_28 : cChain 4 (slabV 4 (tauV4 28)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_20_668_454

theorem chC_4_29 : cChain 4 (slabV 4 (tauV4 29)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_20_674_454

theorem chC_4_30 : cChain 4 (slabV 4 (tauV4 30)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_20_668_462

theorem chC_4_31 : cChain 4 (slabV 4 (tauV4 31)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_20_677_462

/-- **Wall leaf (cusp 4, cell 33)**: the 8 wall triangles of cell `33` give its `Ψ_M`-image. -/
theorem wallCell_4_33 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 33), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (33 : Fin 192) • (PsiM.f 2) (Pi.single (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 33) = {24, 25, 26, 27, 28, 29, 30, 31} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_33) LP_4_33_inj LP_4_33_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_24, chC_4_25, chC_4_26, chC_4_27, chC_4_28, chC_4_29, chC_4_30, chC_4_31]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 0).1.1.idx) * qInc (LP_4_33 0).1.1.idx (LP_4_33 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 1).1.1.idx) * qInc (LP_4_33 1).1.1.idx (LP_4_33 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 2).1.1.idx) * qInc (LP_4_33 2).1.1.idx (LP_4_33 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 3).1.1.idx) * qInc (LP_4_33 3).1.1.idx (LP_4_33 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 4).1.1.idx) * qInc (LP_4_33 4).1.1.idx (LP_4_33 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 5).1.1.idx) * qInc (LP_4_33 5).1.1.idx (LP_4_33 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 6).1.1.idx) * qInc (LP_4_33 6).1.1.idx (LP_4_33 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 7).1.1.idx) * qInc (LP_4_33 7).1.1.idx (LP_4_33 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (33 : Fin 192) = -1 := by decide +kernel
  have a24 : coefV4 24 = -1 := by decide +kernel
  have a25 : coefV4 25 = 1 := by decide +kernel
  have a26 : coefV4 26 = 1 := by decide +kernel
  have a27 : coefV4 27 = -1 := by decide +kernel
  have a28 : coefV4 28 = 1 := by decide +kernel
  have a29 : coefV4 29 = -1 := by decide +kernel
  have a30 : coefV4 30 = -1 := by decide +kernel
  have a31 : coefV4 31 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a24, a25, a26, a27, a28, a29, a30, a31]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 36 (root face 96) -/

/-- The eight `(f,u)`-chains of the root face of cell `36`. -/
def LP_4_36 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨238⟩, ⟨662⟩), by decide +kernel⟩,
  ⟨(⟨238⟩, ⟨674⟩), by decide +kernel⟩,
  ⟨(⟨394⟩, ⟨662⟩), by decide +kernel⟩,
  ⟨(⟨394⟩, ⟨677⟩), by decide +kernel⟩,
  ⟨(⟨454⟩, ⟨668⟩), by decide +kernel⟩,
  ⟨(⟨454⟩, ⟨674⟩), by decide +kernel⟩,
  ⟨(⟨462⟩, ⟨668⟩), by decide +kernel⟩,
  ⟨(⟨462⟩, ⟨677⟩), by decide +kernel⟩]

theorem LP_4_36_inj : Function.Injective LP_4_36 := by decide +kernel

theorem LP_4_36_surj : Function.Surjective LP_4_36 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨238⟩, ⟨394⟩, ⟨454⟩, ⟨462⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨238⟩ : QbarCW.Cell) = {⟨662⟩, ⟨674⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨394⟩ : QbarCW.Cell) = {⟨662⟩, ⟨677⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨454⟩ : QbarCW.Cell) = {⟨668⟩, ⟨674⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨462⟩ : QbarCW.Cell) = {⟨668⟩, ⟨677⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_96 : cChain 4 (slabV 4 (tauV4 96)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_34_774_267

theorem chC_4_97 : cChain 4 (slabV 4 (tauV4 97)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_34_797_267

theorem chC_4_98 : cChain 4 (slabV 4 (tauV4 98)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_34_774_327

theorem chC_4_99 : cChain 4 (slabV 4 (tauV4 99)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_34_800_327

theorem chC_4_100 : cChain 4 (slabV 4 (tauV4 100)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_34_648_435

theorem chC_4_101 : cChain 4 (slabV 4 (tauV4 101)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_34_797_435

theorem chC_4_102 : cChain 4 (slabV 4 (tauV4 102)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_34_648_443

theorem chC_4_103 : cChain 4 (slabV 4 (tauV4 103)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_34_800_443

/-- **Wall leaf (cusp 4, cell 36)**: the 8 wall triangles of cell `36` give its `Ψ_M`-image. -/
theorem wallCell_4_36 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 36), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (36 : Fin 192) • (PsiM.f 2) (Pi.single (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 36) = {96, 97, 98, 99, 100, 101, 102, 103} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_36) LP_4_36_inj LP_4_36_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_96, chC_4_97, chC_4_98, chC_4_99, chC_4_100, chC_4_101, chC_4_102, chC_4_103]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 0).1.1.idx) * qInc (LP_4_36 0).1.1.idx (LP_4_36 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 1).1.1.idx) * qInc (LP_4_36 1).1.1.idx (LP_4_36 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 2).1.1.idx) * qInc (LP_4_36 2).1.1.idx (LP_4_36 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 3).1.1.idx) * qInc (LP_4_36 3).1.1.idx (LP_4_36 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 4).1.1.idx) * qInc (LP_4_36 4).1.1.idx (LP_4_36 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 5).1.1.idx) * qInc (LP_4_36 5).1.1.idx (LP_4_36 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 6).1.1.idx) * qInc (LP_4_36 6).1.1.idx (LP_4_36 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 7).1.1.idx) * qInc (LP_4_36 7).1.1.idx (LP_4_36 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 4 0 (36 : Fin 192) = 1 := by decide +kernel
  have a96 : coefV4 96 = -1 := by decide +kernel
  have a97 : coefV4 97 = 1 := by decide +kernel
  have a98 : coefV4 98 = 1 := by decide +kernel
  have a99 : coefV4 99 = -1 := by decide +kernel
  have a100 : coefV4 100 = 1 := by decide +kernel
  have a101 : coefV4 101 = -1 := by decide +kernel
  have a102 : coefV4 102 = -1 := by decide +kernel
  have a103 : coefV4 103 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a96, a97, a98, a99, a100, a101, a102, a103]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 37 (root face 97) -/

/-- The eight `(f,u)`-chains of the root face of cell `37`. -/
def LP_4_37 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨239⟩, ⟨663⟩), by decide +kernel⟩,
  ⟨(⟨239⟩, ⟨692⟩), by decide +kernel⟩,
  ⟨(⟨395⟩, ⟨663⟩), by decide +kernel⟩,
  ⟨(⟨395⟩, ⟨695⟩), by decide +kernel⟩,
  ⟨(⟨450⟩, ⟨686⟩), by decide +kernel⟩,
  ⟨(⟨450⟩, ⟨692⟩), by decide +kernel⟩,
  ⟨(⟨458⟩, ⟨686⟩), by decide +kernel⟩,
  ⟨(⟨458⟩, ⟨695⟩), by decide +kernel⟩]

theorem LP_4_37_inj : Function.Injective LP_4_37 := by decide +kernel

theorem LP_4_37_surj : Function.Surjective LP_4_37 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨239⟩, ⟨395⟩, ⟨450⟩, ⟨458⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨239⟩ : QbarCW.Cell) = {⟨663⟩, ⟨692⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨395⟩ : QbarCW.Cell) = {⟨663⟩, ⟨695⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨450⟩ : QbarCW.Cell) = {⟨686⟩, ⟨692⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨458⟩ : QbarCW.Cell) = {⟨686⟩, ⟨695⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_40 : cChain 4 (slabV 4 (tauV4 40)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_22_773_266

theorem chC_4_41 : cChain 4 (slabV 4 (tauV4 41)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_22_782_266

theorem chC_4_42 : cChain 4 (slabV 4 (tauV4 42)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_22_773_326

theorem chC_4_43 : cChain 4 (slabV 4 (tauV4 43)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_22_785_326

theorem chC_4_44 : cChain 4 (slabV 4 (tauV4 44)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_439
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_22_630_439

theorem chC_4_45 : cChain 4 (slabV 4 (tauV4 45)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_439
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_22_782_439

theorem chC_4_46 : cChain 4 (slabV 4 (tauV4 46)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_447
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_22_630_447

theorem chC_4_47 : cChain 4 (slabV 4 (tauV4 47)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_447
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_22_785_447

/-- **Wall leaf (cusp 4, cell 37)**: the 8 wall triangles of cell `37` give its `Ψ_M`-image. -/
theorem wallCell_4_37 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 37), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (37 : Fin 192) • (PsiM.f 2) (Pi.single (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 37) = {40, 41, 42, 43, 44, 45, 46, 47} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_37) LP_4_37_inj LP_4_37_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_40, chC_4_41, chC_4_42, chC_4_43, chC_4_44, chC_4_45, chC_4_46, chC_4_47]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 0).1.1.idx) * qInc (LP_4_37 0).1.1.idx (LP_4_37 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 1).1.1.idx) * qInc (LP_4_37 1).1.1.idx (LP_4_37 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 2).1.1.idx) * qInc (LP_4_37 2).1.1.idx (LP_4_37 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 3).1.1.idx) * qInc (LP_4_37 3).1.1.idx (LP_4_37 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 4).1.1.idx) * qInc (LP_4_37 4).1.1.idx (LP_4_37 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 5).1.1.idx) * qInc (LP_4_37 5).1.1.idx (LP_4_37 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 6).1.1.idx) * qInc (LP_4_37 6).1.1.idx (LP_4_37 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 7).1.1.idx) * qInc (LP_4_37 7).1.1.idx (LP_4_37 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 4 0 (37 : Fin 192) = -1 := by decide +kernel
  have a40 : coefV4 40 = 1 := by decide +kernel
  have a41 : coefV4 41 = -1 := by decide +kernel
  have a42 : coefV4 42 = -1 := by decide +kernel
  have a43 : coefV4 43 = 1 := by decide +kernel
  have a44 : coefV4 44 = -1 := by decide +kernel
  have a45 : coefV4 45 = 1 := by decide +kernel
  have a46 : coefV4 46 = 1 := by decide +kernel
  have a47 : coefV4 47 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a40, a41, a42, a43, a44, a45, a46, a47]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 38 (root face 98) -/

/-- The eight `(f,u)`-chains of the root face of cell `38`. -/
def LP_4_38 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨206⟩, ⟨806⟩), by decide +kernel⟩,
  ⟨(⟨206⟩, ⟨815⟩), by decide +kernel⟩,
  ⟨(⟨370⟩, ⟨806⟩), by decide +kernel⟩,
  ⟨(⟨370⟩, ⟨818⟩), by decide +kernel⟩,
  ⟨(⟨455⟩, ⟨669⟩), by decide +kernel⟩,
  ⟨(⟨455⟩, ⟨815⟩), by decide +kernel⟩,
  ⟨(⟨463⟩, ⟨669⟩), by decide +kernel⟩,
  ⟨(⟨463⟩, ⟨818⟩), by decide +kernel⟩]

theorem LP_4_38_inj : Function.Injective LP_4_38 := by decide +kernel

theorem LP_4_38_surj : Function.Surjective LP_4_38 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨206⟩, ⟨370⟩, ⟨455⟩, ⟨463⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨206⟩ : QbarCW.Cell) = {⟨806⟩, ⟨815⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨370⟩ : QbarCW.Cell) = {⟨806⟩, ⟨818⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨455⟩ : QbarCW.Cell) = {⟨669⟩, ⟨815⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨463⟩ : QbarCW.Cell) = {⟨669⟩, ⟨818⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_72 : cChain 4 (slabV 4 (tauV4 72)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_624_299

theorem chC_4_73 : cChain 4 (slabV 4 (tauV4 73)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_653_299

theorem chC_4_74 : cChain 4 (slabV 4 (tauV4 74)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_624_351

theorem chC_4_75 : cChain 4 (slabV 4 (tauV4 75)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_656_351

theorem chC_4_76 : cChain 4 (slabV 4 (tauV4 76)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_647_434

theorem chC_4_77 : cChain 4 (slabV 4 (tauV4 77)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_653_434

theorem chC_4_78 : cChain 4 (slabV 4 (tauV4 78)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_647_442

theorem chC_4_79 : cChain 4 (slabV 4 (tauV4 79)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_656_442

/-- **Wall leaf (cusp 4, cell 38)**: the 8 wall triangles of cell `38` give its `Ψ_M`-image. -/
theorem wallCell_4_38 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 38), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (38 : Fin 192) • (PsiM.f 2) (Pi.single (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 38) = {72, 73, 74, 75, 76, 77, 78, 79} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_38) LP_4_38_inj LP_4_38_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_72, chC_4_73, chC_4_74, chC_4_75, chC_4_76, chC_4_77, chC_4_78, chC_4_79]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 0).1.1.idx) * qInc (LP_4_38 0).1.1.idx (LP_4_38 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 1).1.1.idx) * qInc (LP_4_38 1).1.1.idx (LP_4_38 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 2).1.1.idx) * qInc (LP_4_38 2).1.1.idx (LP_4_38 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 3).1.1.idx) * qInc (LP_4_38 3).1.1.idx (LP_4_38 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 4).1.1.idx) * qInc (LP_4_38 4).1.1.idx (LP_4_38 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 5).1.1.idx) * qInc (LP_4_38 5).1.1.idx (LP_4_38 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 6).1.1.idx) * qInc (LP_4_38 6).1.1.idx (LP_4_38 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 7).1.1.idx) * qInc (LP_4_38 7).1.1.idx (LP_4_38 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (38 : Fin 192) = 1 := by decide +kernel
  have a72 : coefV4 72 = 1 := by decide +kernel
  have a73 : coefV4 73 = -1 := by decide +kernel
  have a74 : coefV4 74 = -1 := by decide +kernel
  have a75 : coefV4 75 = 1 := by decide +kernel
  have a76 : coefV4 76 = -1 := by decide +kernel
  have a77 : coefV4 77 = 1 := by decide +kernel
  have a78 : coefV4 78 = 1 := by decide +kernel
  have a79 : coefV4 79 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a72, a73, a74, a75, a76, a77, a78, a79]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 39 (root face 99) -/

/-- The eight `(f,u)`-chains of the root face of cell `39`. -/
def LP_4_39 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨207⟩, ⟨807⟩), by decide +kernel⟩,
  ⟨(⟨207⟩, ⟨830⟩), by decide +kernel⟩,
  ⟨(⟨371⟩, ⟨807⟩), by decide +kernel⟩,
  ⟨(⟨371⟩, ⟨833⟩), by decide +kernel⟩,
  ⟨(⟨451⟩, ⟨687⟩), by decide +kernel⟩,
  ⟨(⟨451⟩, ⟨830⟩), by decide +kernel⟩,
  ⟨(⟨459⟩, ⟨687⟩), by decide +kernel⟩,
  ⟨(⟨459⟩, ⟨833⟩), by decide +kernel⟩]

theorem LP_4_39_inj : Function.Injective LP_4_39 := by decide +kernel


end

end Work.BridgeSquare.SlabBuild
