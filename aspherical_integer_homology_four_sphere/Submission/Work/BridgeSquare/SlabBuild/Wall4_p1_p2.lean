import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts4
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p1_p1

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



theorem LP_4_26_surj : Function.Surjective LP_4_26 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨202⟩, ⟨322⟩, ⟨423⟩, ⟨431⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨202⟩ : QbarCW.Cell) = {⟨839⟩, ⟨845⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨322⟩ : QbarCW.Cell) = {⟨839⟩, ⟨848⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨423⟩ : QbarCW.Cell) = {⟨705⟩, ⟨845⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨431⟩ : QbarCW.Cell) = {⟨705⟩, ⟨848⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_32 : cChain 4 (slabV 4 (tauV4 32)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_21_579_303

theorem chC_4_33 : cChain 4 (slabV 4 (tauV4 33)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_21_614_303

theorem chC_4_34 : cChain 4 (slabV 4 (tauV4 34)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_21_579_399

theorem chC_4_35 : cChain 4 (slabV 4 (tauV4 35)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_21_617_399

theorem chC_4_36 : cChain 4 (slabV 4 (tauV4 36)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_21_608_466

theorem chC_4_37 : cChain 4 (slabV 4 (tauV4 37)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_21_614_466

theorem chC_4_38 : cChain 4 (slabV 4 (tauV4 38)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_21_608_474

theorem chC_4_39 : cChain 4 (slabV 4 (tauV4 39)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_21_617_474

/-- **Wall leaf (cusp 4, cell 26)**: the 8 wall triangles of cell `26` give its `Ψ_M`-image. -/
theorem wallCell_4_26 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 26), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (26 : Fin 192) • (PsiM.f 2) (Pi.single (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 26) = {32, 33, 34, 35, 36, 37, 38, 39} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_26) LP_4_26_inj LP_4_26_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_32, chC_4_33, chC_4_34, chC_4_35, chC_4_36, chC_4_37, chC_4_38, chC_4_39]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 0).1.1.idx) * qInc (LP_4_26 0).1.1.idx (LP_4_26 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 1).1.1.idx) * qInc (LP_4_26 1).1.1.idx (LP_4_26 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 2).1.1.idx) * qInc (LP_4_26 2).1.1.idx (LP_4_26 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 3).1.1.idx) * qInc (LP_4_26 3).1.1.idx (LP_4_26 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 4).1.1.idx) * qInc (LP_4_26 4).1.1.idx (LP_4_26 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 5).1.1.idx) * qInc (LP_4_26 5).1.1.idx (LP_4_26 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 6).1.1.idx) * qInc (LP_4_26 6).1.1.idx (LP_4_26 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 7).1.1.idx) * qInc (LP_4_26 7).1.1.idx (LP_4_26 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (26 : Fin 192) = -1 := by decide +kernel
  have a32 : coefV4 32 = -1 := by decide +kernel
  have a33 : coefV4 33 = 1 := by decide +kernel
  have a34 : coefV4 34 = 1 := by decide +kernel
  have a35 : coefV4 35 = -1 := by decide +kernel
  have a36 : coefV4 36 = 1 := by decide +kernel
  have a37 : coefV4 37 = -1 := by decide +kernel
  have a38 : coefV4 38 = -1 := by decide +kernel
  have a39 : coefV4 39 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a32, a33, a34, a35, a36, a37, a38, a39]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 27 (root face 85) -/

/-- The eight `(f,u)`-chains of the root face of cell `27`. -/
def LP_4_27 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨203⟩, ⟨840⟩), by decide +kernel⟩,
  ⟨(⟨203⟩, ⟨857⟩), by decide +kernel⟩,
  ⟨(⟨323⟩, ⟨840⟩), by decide +kernel⟩,
  ⟨(⟨323⟩, ⟨860⟩), by decide +kernel⟩,
  ⟨(⟨419⟩, ⟨720⟩), by decide +kernel⟩,
  ⟨(⟨419⟩, ⟨857⟩), by decide +kernel⟩,
  ⟨(⟨427⟩, ⟨720⟩), by decide +kernel⟩,
  ⟨(⟨427⟩, ⟨860⟩), by decide +kernel⟩]

theorem LP_4_27_inj : Function.Injective LP_4_27 := by decide +kernel

theorem LP_4_27_surj : Function.Surjective LP_4_27 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨203⟩, ⟨323⟩, ⟨419⟩, ⟨427⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨203⟩ : QbarCW.Cell) = {⟨840⟩, ⟨857⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨323⟩ : QbarCW.Cell) = {⟨840⟩, ⟨860⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨419⟩ : QbarCW.Cell) = {⟨720⟩, ⟨857⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨427⟩ : QbarCW.Cell) = {⟨720⟩, ⟨860⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_0 : cChain 4 (slabV 4 (tauV4 0)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_16_578_302

theorem chC_4_1 : cChain 4 (slabV 4 (tauV4 1)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_16_593_302

theorem chC_4_2 : cChain 4 (slabV 4 (tauV4 2)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_16_578_398

theorem chC_4_3 : cChain 4 (slabV 4 (tauV4 3)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_16_596_398

theorem chC_4_4 : cChain 4 (slabV 4 (tauV4 4)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_16_587_470

theorem chC_4_5 : cChain 4 (slabV 4 (tauV4 5)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_16_593_470

theorem chC_4_6 : cChain 4 (slabV 4 (tauV4 6)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_16_587_478

theorem chC_4_7 : cChain 4 (slabV 4 (tauV4 7)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_16_596_478

/-- **Wall leaf (cusp 4, cell 27)**: the 8 wall triangles of cell `27` give its `Ψ_M`-image. -/
theorem wallCell_4_27 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 27), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (27 : Fin 192) • (PsiM.f 2) (Pi.single (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 27) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_27) LP_4_27_inj LP_4_27_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_0, chC_4_1, chC_4_2, chC_4_3, chC_4_4, chC_4_5, chC_4_6, chC_4_7]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 0).1.1.idx) * qInc (LP_4_27 0).1.1.idx (LP_4_27 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 1).1.1.idx) * qInc (LP_4_27 1).1.1.idx (LP_4_27 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 2).1.1.idx) * qInc (LP_4_27 2).1.1.idx (LP_4_27 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 3).1.1.idx) * qInc (LP_4_27 3).1.1.idx (LP_4_27 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 4).1.1.idx) * qInc (LP_4_27 4).1.1.idx (LP_4_27 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 5).1.1.idx) * qInc (LP_4_27 5).1.1.idx (LP_4_27 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 6).1.1.idx) * qInc (LP_4_27 6).1.1.idx (LP_4_27 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 7).1.1.idx) * qInc (LP_4_27 7).1.1.idx (LP_4_27 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (27 : Fin 192) = 1 := by decide +kernel
  have a0 : coefV4 0 = 1 := by decide +kernel
  have a1 : coefV4 1 = -1 := by decide +kernel
  have a2 : coefV4 2 = -1 := by decide +kernel
  have a3 : coefV4 3 = 1 := by decide +kernel
  have a4 : coefV4 4 = -1 := by decide +kernel
  have a5 : coefV4 5 = 1 := by decide +kernel
  have a6 : coefV4 6 = 1 := by decide +kernel
  have a7 : coefV4 7 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a0, a1, a2, a3, a4, a5, a6, a7]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 30 (root face 89) -/

/-- The eight `(f,u)`-chains of the root face of cell `30`. -/
def LP_4_30 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨298⟩, ⟨623⟩), by decide +kernel⟩,
  ⟨(⟨298⟩, ⟨635⟩), by decide +kernel⟩,
  ⟨(⟨350⟩, ⟨623⟩), by decide +kernel⟩,
  ⟨(⟨350⟩, ⟨638⟩), by decide +kernel⟩,
  ⟨(⟨438⟩, ⟨629⟩), by decide +kernel⟩,
  ⟨(⟨438⟩, ⟨635⟩), by decide +kernel⟩,
  ⟨(⟨446⟩, ⟨629⟩), by decide +kernel⟩,
  ⟨(⟨446⟩, ⟨638⟩), by decide +kernel⟩]

theorem LP_4_30_inj : Function.Injective LP_4_30 := by decide +kernel



end

end Work.BridgeSquare.SlabBuild
