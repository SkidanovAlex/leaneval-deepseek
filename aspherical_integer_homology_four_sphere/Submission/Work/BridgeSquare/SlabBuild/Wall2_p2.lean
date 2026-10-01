import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts2
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall2_p1

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



theorem chC_2_20 : cChain 2 (slabV 2 (tauV2 20)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464
      = mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_10_678_464

theorem chC_2_21 : cChain 2 (slabV 2 (tauV2 21)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_464
      = mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_10_819_464

theorem chC_2_22 : cChain 2 (slabV 2 (tauV2 22)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_480
      = mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_10_597_480

theorem chC_2_23 : cChain 2 (slabV 2 (tauV2 23)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_480
      = mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_10_750_480

/-- **Wall leaf (cusp 2, cell 94)**: the 8 wall triangles of cell `94` give its `Ψ_M`-image. -/
theorem wallCell_2_94 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx2 => cellV2 j = 94), coefV2 j • cChain 2 (slabV 2 (tauV2 j)))
      = planeCycleVec 2 0 (94 : Fin 192) • (PsiM.f 2) (Pi.single (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx2 => cellV2 j = 94) = {16, 17, 18, 19, 20, 21, 22, 23} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_2_94) LP_2_94_inj LP_2_94_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_2_16, chC_2_17, chC_2_18, chC_2_19, chC_2_20, chC_2_21, chC_2_22, chC_2_23]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_94 0).1.1.idx) * qInc (LP_2_94 0).1.1.idx (LP_2_94 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_94 1).1.1.idx) * qInc (LP_2_94 1).1.1.idx (LP_2_94 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_94 2).1.1.idx) * qInc (LP_2_94 2).1.1.idx (LP_2_94 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_94 3).1.1.idx) * qInc (LP_2_94 3).1.1.idx (LP_2_94 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_94 4).1.1.idx) * qInc (LP_2_94 4).1.1.idx (LP_2_94 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_94 5).1.1.idx) * qInc (LP_2_94 5).1.1.idx (LP_2_94 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_94 6).1.1.idx) * qInc (LP_2_94 6).1.1.idx (LP_2_94 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_94 7).1.1.idx) * qInc (LP_2_94 7).1.1.idx (LP_2_94 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 2 0 (94 : Fin 192) = -1 := by decide +kernel
  have a16 : coefV2 16 = 1 := by decide +kernel
  have a17 : coefV2 17 = -1 := by decide +kernel
  have a18 : coefV2 18 = -1 := by decide +kernel
  have a19 : coefV2 19 = 1 := by decide +kernel
  have a20 : coefV2 20 = -1 := by decide +kernel
  have a21 : coefV2 21 = 1 := by decide +kernel
  have a22 : coefV2 22 = 1 := by decide +kernel
  have a23 : coefV2 23 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a16, a17, a18, a19, a20, a21, a22, a23]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 2, cell 176 (root face 170) -/

/-- The eight `(f,u)`-chains of the root face of cell `176`. -/
def LP_2_176 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨340⟩, ⟨801⟩), by decide +kernel⟩,
  ⟨(⟨340⟩, ⟨861⟩), by decide +kernel⟩,
  ⟨(⟨364⟩, ⟨657⟩), by decide +kernel⟩,
  ⟨(⟨364⟩, ⟨729⟩), by decide +kernel⟩,
  ⟨(⟨428⟩, ⟨729⟩), by decide +kernel⟩,
  ⟨(⟨428⟩, ⟨861⟩), by decide +kernel⟩,
  ⟨(⟨444⟩, ⟨657⟩), by decide +kernel⟩,
  ⟨(⟨444⟩, ⟨801⟩), by decide +kernel⟩]

theorem LP_2_176_inj : Function.Injective LP_2_176 := by decide +kernel

theorem LP_2_176_surj : Function.Surjective LP_2_176 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨340⟩, ⟨364⟩, ⟨428⟩, ⟨444⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨340⟩ : QbarCW.Cell) = {⟨801⟩, ⟨861⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨364⟩ : QbarCW.Cell) = {⟨657⟩, ⟨729⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨428⟩ : QbarCW.Cell) = {⟨729⟩, ⟨861⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨444⟩ : QbarCW.Cell) = {⟨657⟩, ⟨801⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_2_0 : cChain 2 (slabV 2 (tauV2 0)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_340
      = mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_8_801_340

theorem chC_2_1 : cChain 2 (slabV 2 (tauV2 1)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_340
      = mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_8_861_340

theorem chC_2_2 : cChain 2 (slabV 2 (tauV2 2)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_364
      = mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_8_657_364

theorem chC_2_3 : cChain 2 (slabV 2 (tauV2 3)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_364
      = mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_8_729_364

theorem chC_2_4 : cChain 2 (slabV 2 (tauV2 4)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_428
      = mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_8_729_428

theorem chC_2_5 : cChain 2 (slabV 2 (tauV2 5)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428
      = mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_8_861_428

theorem chC_2_6 : cChain 2 (slabV 2 (tauV2 6)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444
      = mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_8_657_444

theorem chC_2_7 : cChain 2 (slabV 2 (tauV2 7)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444
      = mkSimplex (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_176 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_8_801_444

/-- **Wall leaf (cusp 2, cell 176)**: the 8 wall triangles of cell `176` give its `Ψ_M`-image. -/
theorem wallCell_2_176 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx2 => cellV2 j = 176), coefV2 j • cChain 2 (slabV 2 (tauV2 j)))
      = planeCycleVec 2 0 (176 : Fin 192) • (PsiM.f 2) (Pi.single (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx2 => cellV2 j = 176) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_2_176) LP_2_176_inj LP_2_176_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_2_0, chC_2_1, chC_2_2, chC_2_3, chC_2_4, chC_2_5, chC_2_6, chC_2_7]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_176 0).1.1.idx) * qInc (LP_2_176 0).1.1.idx (LP_2_176 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_176 1).1.1.idx) * qInc (LP_2_176 1).1.1.idx (LP_2_176 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_176 2).1.1.idx) * qInc (LP_2_176 2).1.1.idx (LP_2_176 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_176 3).1.1.idx) * qInc (LP_2_176 3).1.1.idx (LP_2_176 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_176 4).1.1.idx) * qInc (LP_2_176 4).1.1.idx (LP_2_176 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_176 5).1.1.idx) * qInc (LP_2_176 5).1.1.idx (LP_2_176 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_176 6).1.1.idx) * qInc (LP_2_176 6).1.1.idx (LP_2_176 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_176 7).1.1.idx) * qInc (LP_2_176 7).1.1.idx (LP_2_176 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 2 0 (176 : Fin 192) = 1 := by decide +kernel
  have a0 : coefV2 0 = -1 := by decide +kernel
  have a1 : coefV2 1 = 1 := by decide +kernel
  have a2 : coefV2 2 = 1 := by decide +kernel
  have a3 : coefV2 3 = -1 := by decide +kernel
  have a4 : coefV2 4 = 1 := by decide +kernel
  have a5 : coefV2 5 = -1 := by decide +kernel
  have a6 : coefV2 6 = -1 := by decide +kernel
  have a7 : coefV2 7 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a0, a1, a2, a3, a4, a5, a6, a7]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 2, cell 182 (root face 177) -/

/-- The eight `(f,u)`-chains of the root face of cell `182`. -/
def LP_2_182 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨388⟩, ⟨768⟩), by decide +kernel⟩,
  ⟨(⟨388⟩, ⟨834⟩), by decide +kernel⟩,
  ⟨(⟨412⟩, ⟨618⟩), by decide +kernel⟩,
  ⟨(⟨412⟩, ⟨696⟩), by decide +kernel⟩,
  ⟨(⟨460⟩, ⟨696⟩), by decide +kernel⟩,
  ⟨(⟨460⟩, ⟨834⟩), by decide +kernel⟩,
  ⟨(⟨476⟩, ⟨618⟩), by decide +kernel⟩,
  ⟨(⟨476⟩, ⟨768⟩), by decide +kernel⟩]


end

end Work.BridgeSquare.SlabBuild
