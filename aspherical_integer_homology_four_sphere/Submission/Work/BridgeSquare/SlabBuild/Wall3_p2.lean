import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts3
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall3_p1

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



theorem chC_3_12 : cChain 3 (slabV 3 (tauV3 12)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_572
      = mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_13_642_572

theorem chC_3_13 : cChain 3 (slabV 3 (tauV3 13)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_572
      = mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_13_789_572

theorem chC_3_14 : cChain 3 (slabV 3 (tauV3 14)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_576
      = mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_13_600_576

theorem chC_3_15 : cChain 3 (slabV 3 (tauV3 15)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_576
      = mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_13_753_576

/-- **Wall leaf (cusp 3, cell 83)**: the 8 wall triangles of cell `83` give its `Ψ_M`-image. -/
theorem wallCell_3_83 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx3 => cellV3 j = 83), coefV3 j • cChain 3 (slabV 3 (tauV3 j)))
      = planeCycleVec 3 0 (83 : Fin 192) • (PsiM.f 2) (Pi.single (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx3 => cellV3 j = 83) = {8, 9, 10, 11, 12, 13, 14, 15} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_3_83) LP_3_83_inj LP_3_83_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_3_8, chC_3_9, chC_3_10, chC_3_11, chC_3_12, chC_3_13, chC_3_14, chC_3_15]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_83 0).1.1.idx) * qInc (LP_3_83 0).1.1.idx (LP_3_83 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_83 1).1.1.idx) * qInc (LP_3_83 1).1.1.idx (LP_3_83 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_83 2).1.1.idx) * qInc (LP_3_83 2).1.1.idx (LP_3_83 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_83 3).1.1.idx) * qInc (LP_3_83 3).1.1.idx (LP_3_83 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_83 4).1.1.idx) * qInc (LP_3_83 4).1.1.idx (LP_3_83 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_83 5).1.1.idx) * qInc (LP_3_83 5).1.1.idx (LP_3_83 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_83 6).1.1.idx) * qInc (LP_3_83 6).1.1.idx (LP_3_83 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_83 7).1.1.idx) * qInc (LP_3_83 7).1.1.idx (LP_3_83 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 3 0 (83 : Fin 192) = -1 := by decide +kernel
  have a8 : coefV3 8 = 1 := by decide +kernel
  have a9 : coefV3 9 = -1 := by decide +kernel
  have a10 : coefV3 10 = -1 := by decide +kernel
  have a11 : coefV3 11 = 1 := by decide +kernel
  have a12 : coefV3 12 = -1 := by decide +kernel
  have a13 : coefV3 13 = 1 := by decide +kernel
  have a14 : coefV3 14 = 1 := by decide +kernel
  have a15 : coefV3 15 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a8, a9, a10, a11, a12, a13, a14, a15]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 3, cell 165 (root face 143) -/

/-- The eight `(f,u)`-chains of the root face of cell `165`. -/
def LP_3_165 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨484⟩, ⟨837⟩), by decide +kernel⟩,
  ⟨(⟨484⟩, ⟨864⟩), by decide +kernel⟩,
  ⟨(⟨500⟩, ⟨699⟩), by decide +kernel⟩,
  ⟨(⟨500⟩, ⟨732⟩), by decide +kernel⟩,
  ⟨(⟨548⟩, ⟨732⟩), by decide +kernel⟩,
  ⟨(⟨548⟩, ⟨864⟩), by decide +kernel⟩,
  ⟨(⟨552⟩, ⟨699⟩), by decide +kernel⟩,
  ⟨(⟨552⟩, ⟨837⟩), by decide +kernel⟩]

theorem LP_3_165_inj : Function.Injective LP_3_165 := by decide +kernel

theorem LP_3_165_surj : Function.Surjective LP_3_165 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨484⟩, ⟨500⟩, ⟨548⟩, ⟨552⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨484⟩ : QbarCW.Cell) = {⟨837⟩, ⟨864⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨500⟩ : QbarCW.Cell) = {⟨699⟩, ⟨732⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨548⟩ : QbarCW.Cell) = {⟨732⟩, ⟨864⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨552⟩ : QbarCW.Cell) = {⟨699⟩, ⟨837⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_3_0 : cChain 3 (slabV 3 (tauV3 0)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484
      = mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_12_837_484

theorem chC_3_1 : cChain 3 (slabV 3 (tauV3 1)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484
      = mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_12_864_484

theorem chC_3_2 : cChain 3 (slabV 3 (tauV3 2)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500
      = mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_12_699_500

theorem chC_3_3 : cChain 3 (slabV 3 (tauV3 3)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500
      = mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_12_732_500

theorem chC_3_4 : cChain 3 (slabV 3 (tauV3 4)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548
      = mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_12_732_548

theorem chC_3_5 : cChain 3 (slabV 3 (tauV3 5)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_548
      = mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_12_864_548

theorem chC_3_6 : cChain 3 (slabV 3 (tauV3 6)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_552
      = mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_12_699_552

theorem chC_3_7 : cChain 3 (slabV 3 (tauV3 7)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_552
      = mkSimplex (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_165 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_12_837_552

/-- **Wall leaf (cusp 3, cell 165)**: the 8 wall triangles of cell `165` give its `Ψ_M`-image. -/
theorem wallCell_3_165 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx3 => cellV3 j = 165), coefV3 j • cChain 3 (slabV 3 (tauV3 j)))
      = planeCycleVec 3 0 (165 : Fin 192) • (PsiM.f 2) (Pi.single (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx3 => cellV3 j = 165) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_3_165) LP_3_165_inj LP_3_165_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_3_0, chC_3_1, chC_3_2, chC_3_3, chC_3_4, chC_3_5, chC_3_6, chC_3_7]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_165 0).1.1.idx) * qInc (LP_3_165 0).1.1.idx (LP_3_165 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_165 1).1.1.idx) * qInc (LP_3_165 1).1.1.idx (LP_3_165 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_165 2).1.1.idx) * qInc (LP_3_165 2).1.1.idx (LP_3_165 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_165 3).1.1.idx) * qInc (LP_3_165 3).1.1.idx (LP_3_165 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_165 4).1.1.idx) * qInc (LP_3_165 4).1.1.idx (LP_3_165 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_165 5).1.1.idx) * qInc (LP_3_165 5).1.1.idx (LP_3_165 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_165 6).1.1.idx) * qInc (LP_3_165 6).1.1.idx (LP_3_165 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_165 7).1.1.idx) * qInc (LP_3_165 7).1.1.idx (LP_3_165 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 3 0 (165 : Fin 192) = 1 := by decide +kernel
  have a0 : coefV3 0 = -1 := by decide +kernel
  have a1 : coefV3 1 = 1 := by decide +kernel
  have a2 : coefV3 2 = 1 := by decide +kernel
  have a3 : coefV3 3 = -1 := by decide +kernel
  have a4 : coefV3 4 = 1 := by decide +kernel
  have a5 : coefV3 5 = -1 := by decide +kernel
  have a6 : coefV3 6 = -1 := by decide +kernel
  have a7 : coefV3 7 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a0, a1, a2, a3, a4, a5, a6, a7]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 3, cell 171 (root face 157) -/

/-- The eight `(f,u)`-chains of the root face of cell `171`. -/
def LP_3_171 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨516⟩, ⟨822⟩), by decide +kernel⟩,
  ⟨(⟨516⟩, ⟨852⟩), by decide +kernel⟩,
  ⟨(⟨532⟩, ⟨681⟩), by decide +kernel⟩,
  ⟨(⟨532⟩, ⟨717⟩), by decide +kernel⟩,
  ⟨(⟨564⟩, ⟨717⟩), by decide +kernel⟩,
  ⟨(⟨564⟩, ⟨852⟩), by decide +kernel⟩,
  ⟨(⟨568⟩, ⟨681⟩), by decide +kernel⟩,
  ⟨(⟨568⟩, ⟨822⟩), by decide +kernel⟩]


end

end Work.BridgeSquare.SlabBuild
