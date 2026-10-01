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



end

end Work.BridgeSquare.SlabBuild
