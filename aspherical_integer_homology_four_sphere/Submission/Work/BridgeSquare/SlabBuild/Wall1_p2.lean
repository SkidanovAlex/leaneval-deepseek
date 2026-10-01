import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts1
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall1_p1

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



theorem chC_1_12 : cChain 1 (slabV 1 (tauV1 12)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_316
      = mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_5_615_316

theorem chC_1_13 : cChain 1 (slabV 1 (tauV1 13)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_316
      = mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_5_654_316

theorem chC_1_14 : cChain 1 (slabV 1 (tauV1 14)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_320
      = mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_5_594_320

theorem chC_1_15 : cChain 1 (slabV 1 (tauV1 15)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_320
      = mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_5_636_320

/-- **Wall leaf (cusp 1, cell 11)**: the 8 wall triangles of cell `11` give its `Ψ_M`-image. -/
theorem wallCell_1_11 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx1 => cellV1 j = 11), coefV1 j • cChain 1 (slabV 1 (tauV1 j)))
      = planeCycleVec 1 0 (11 : Fin 192) • (PsiM.f 2) (Pi.single (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx1 => cellV1 j = 11) = {8, 9, 10, 11, 12, 13, 14, 15} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_1_11) LP_1_11_inj LP_1_11_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_1_8, chC_1_9, chC_1_10, chC_1_11, chC_1_12, chC_1_13, chC_1_14, chC_1_15]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_11 0).1.1.idx) * qInc (LP_1_11 0).1.1.idx (LP_1_11 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_11 1).1.1.idx) * qInc (LP_1_11 1).1.1.idx (LP_1_11 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_11 2).1.1.idx) * qInc (LP_1_11 2).1.1.idx (LP_1_11 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_11 3).1.1.idx) * qInc (LP_1_11 3).1.1.idx (LP_1_11 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_11 4).1.1.idx) * qInc (LP_1_11 4).1.1.idx (LP_1_11 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_11 5).1.1.idx) * qInc (LP_1_11 5).1.1.idx (LP_1_11 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_11 6).1.1.idx) * qInc (LP_1_11 6).1.1.idx (LP_1_11 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_11 7).1.1.idx) * qInc (LP_1_11 7).1.1.idx (LP_1_11 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 1 0 (11 : Fin 192) = -1 := by decide +kernel
  have a8 : coefV1 8 = 1 := by decide +kernel
  have a9 : coefV1 9 = -1 := by decide +kernel
  have a10 : coefV1 10 = -1 := by decide +kernel
  have a11 : coefV1 11 = 1 := by decide +kernel
  have a12 : coefV1 12 = -1 := by decide +kernel
  have a13 : coefV1 13 = 1 := by decide +kernel
  have a14 : coefV1 14 = 1 := by decide +kernel
  have a15 : coefV1 15 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a8, a9, a10, a11, a12, a13, a14, a15]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 1, cell 141 (root face 31) -/

/-- The eight `(f,u)`-chains of the root face of cell `141`. -/
def LP_1_141 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨204⟩, ⟨846⟩), by decide +kernel⟩,
  ⟨(⟨204⟩, ⟨858⟩), by decide +kernel⟩,
  ⟨(⟨208⟩, ⟨816⟩), by decide +kernel⟩,
  ⟨(⟨208⟩, ⟨831⟩), by decide +kernel⟩,
  ⟨(⟨220⟩, ⟨831⟩), by decide +kernel⟩,
  ⟨(⟨220⟩, ⟨858⟩), by decide +kernel⟩,
  ⟨(⟨224⟩, ⟨816⟩), by decide +kernel⟩,
  ⟨(⟨224⟩, ⟨846⟩), by decide +kernel⟩]

theorem LP_1_141_inj : Function.Injective LP_1_141 := by decide +kernel

theorem LP_1_141_surj : Function.Surjective LP_1_141 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨204⟩, ⟨208⟩, ⟨220⟩, ⟨224⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨204⟩ : QbarCW.Cell) = {⟨846⟩, ⟨858⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨208⟩ : QbarCW.Cell) = {⟨816⟩, ⟨831⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨220⟩ : QbarCW.Cell) = {⟨831⟩, ⟨858⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨224⟩ : QbarCW.Cell) = {⟨816⟩, ⟨846⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_1_0 : cChain 1 (slabV 1 (tauV1 0)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_204
      = mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_4_846_204

theorem chC_1_1 : cChain 1 (slabV 1 (tauV1 1)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_204
      = mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_4_858_204

theorem chC_1_2 : cChain 1 (slabV 1 (tauV1 2)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_208
      = mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_4_816_208

theorem chC_1_3 : cChain 1 (slabV 1 (tauV1 3)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_208
      = mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_4_831_208

theorem chC_1_4 : cChain 1 (slabV 1 (tauV1 4)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_220
      = mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_4_831_220

theorem chC_1_5 : cChain 1 (slabV 1 (tauV1 5)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_220
      = mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_4_858_220

theorem chC_1_6 : cChain 1 (slabV 1 (tauV1 6)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_224
      = mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_4_816_224

theorem chC_1_7 : cChain 1 (slabV 1 (tauV1 7)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_224
      = mkSimplex (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_141 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_4_846_224

/-- **Wall leaf (cusp 1, cell 141)**: the 8 wall triangles of cell `141` give its `Ψ_M`-image. -/
theorem wallCell_1_141 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx1 => cellV1 j = 141), coefV1 j • cChain 1 (slabV 1 (tauV1 j)))
      = planeCycleVec 1 0 (141 : Fin 192) • (PsiM.f 2) (Pi.single (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx1 => cellV1 j = 141) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_1_141) LP_1_141_inj LP_1_141_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_1_0, chC_1_1, chC_1_2, chC_1_3, chC_1_4, chC_1_5, chC_1_6, chC_1_7]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_141 0).1.1.idx) * qInc (LP_1_141 0).1.1.idx (LP_1_141 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_141 1).1.1.idx) * qInc (LP_1_141 1).1.1.idx (LP_1_141 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_141 2).1.1.idx) * qInc (LP_1_141 2).1.1.idx (LP_1_141 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_141 3).1.1.idx) * qInc (LP_1_141 3).1.1.idx (LP_1_141 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_141 4).1.1.idx) * qInc (LP_1_141 4).1.1.idx (LP_1_141 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_141 5).1.1.idx) * qInc (LP_1_141 5).1.1.idx (LP_1_141 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_141 6).1.1.idx) * qInc (LP_1_141 6).1.1.idx (LP_1_141 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_141 7).1.1.idx) * qInc (LP_1_141 7).1.1.idx (LP_1_141 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 1 0 (141 : Fin 192) = 1 := by decide +kernel
  have a0 : coefV1 0 = -1 := by decide +kernel
  have a1 : coefV1 1 = 1 := by decide +kernel
  have a2 : coefV1 2 = 1 := by decide +kernel
  have a3 : coefV1 3 = -1 := by decide +kernel
  have a4 : coefV1 4 = 1 := by decide +kernel
  have a5 : coefV1 5 = -1 := by decide +kernel
  have a6 : coefV1 6 = -1 := by decide +kernel
  have a7 : coefV1 7 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a0, a1, a2, a3, a4, a5, a6, a7]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 1, cell 147 (root face 45) -/

/-- The eight `(f,u)`-chains of the root face of cell `147`. -/
def LP_1_147 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨268⟩, ⟨783⟩), by decide +kernel⟩,
  ⟨(⟨268⟩, ⟨798⟩), by decide +kernel⟩,
  ⟨(⟨272⟩, ⟨747⟩), by decide +kernel⟩,
  ⟨(⟨272⟩, ⟨765⟩), by decide +kernel⟩,
  ⟨(⟨284⟩, ⟨765⟩), by decide +kernel⟩,
  ⟨(⟨284⟩, ⟨798⟩), by decide +kernel⟩,
  ⟨(⟨288⟩, ⟨747⟩), by decide +kernel⟩,
  ⟨(⟨288⟩, ⟨783⟩), by decide +kernel⟩]


end

end Work.BridgeSquare.SlabBuild
