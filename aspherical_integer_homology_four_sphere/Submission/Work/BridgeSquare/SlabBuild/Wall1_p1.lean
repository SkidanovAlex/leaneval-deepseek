import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts1
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



/-! ### cusp 1, cell 5 (root face 31) -/

/-- The eight `(f,u)`-chains of the root face of cell `5`. -/
def LP_1_5 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨204⟩, ⟨846⟩), by decide +kernel⟩,
  ⟨(⟨204⟩, ⟨858⟩), by decide +kernel⟩,
  ⟨(⟨208⟩, ⟨816⟩), by decide +kernel⟩,
  ⟨(⟨208⟩, ⟨831⟩), by decide +kernel⟩,
  ⟨(⟨220⟩, ⟨831⟩), by decide +kernel⟩,
  ⟨(⟨220⟩, ⟨858⟩), by decide +kernel⟩,
  ⟨(⟨224⟩, ⟨816⟩), by decide +kernel⟩,
  ⟨(⟨224⟩, ⟨846⟩), by decide +kernel⟩]

theorem LP_1_5_inj : Function.Injective LP_1_5 := by decide +kernel

theorem LP_1_5_surj : Function.Surjective LP_1_5 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨204⟩, ⟨208⟩, ⟨220⟩, ⟨224⟩} := by decide +kernel
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

theorem chC_1_24 : cChain 1 (slabV 1 (tauV1 24)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_236
      = mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_7_711_236

theorem chC_1_25 : cChain 1 (slabV 1 (tauV1 25)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_236
      = mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_7_726_236

theorem chC_1_26 : cChain 1 (slabV 1 (tauV1 26)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_240
      = mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_7_675_240

theorem chC_1_27 : cChain 1 (slabV 1 (tauV1 27)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_240
      = mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_7_693_240

theorem chC_1_28 : cChain 1 (slabV 1 (tauV1 28)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_252
      = mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_7_693_252

theorem chC_1_29 : cChain 1 (slabV 1 (tauV1 29)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_252
      = mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_7_726_252

theorem chC_1_30 : cChain 1 (slabV 1 (tauV1 30)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_256
      = mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_7_675_256

theorem chC_1_31 : cChain 1 (slabV 1 (tauV1 31)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_256
      = mkSimplex (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_5 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_7_711_256

/-- **Wall leaf (cusp 1, cell 5)**: the 8 wall triangles of cell `5` give its `Ψ_M`-image. -/
theorem wallCell_1_5 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx1 => cellV1 j = 5), coefV1 j • cChain 1 (slabV 1 (tauV1 j)))
      = planeCycleVec 1 0 (5 : Fin 192) • (PsiM.f 2) (Pi.single (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx1 => cellV1 j = 5) = {24, 25, 26, 27, 28, 29, 30, 31} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_1_5) LP_1_5_inj LP_1_5_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_1_24, chC_1_25, chC_1_26, chC_1_27, chC_1_28, chC_1_29, chC_1_30, chC_1_31]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_5 0).1.1.idx) * qInc (LP_1_5 0).1.1.idx (LP_1_5 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_5 1).1.1.idx) * qInc (LP_1_5 1).1.1.idx (LP_1_5 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_5 2).1.1.idx) * qInc (LP_1_5 2).1.1.idx (LP_1_5 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_5 3).1.1.idx) * qInc (LP_1_5 3).1.1.idx (LP_1_5 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_5 4).1.1.idx) * qInc (LP_1_5 4).1.1.idx (LP_1_5 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_5 5).1.1.idx) * qInc (LP_1_5 5).1.1.idx (LP_1_5 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_5 6).1.1.idx) * qInc (LP_1_5 6).1.1.idx (LP_1_5 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_5 7).1.1.idx) * qInc (LP_1_5 7).1.1.idx (LP_1_5 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 1 0 (5 : Fin 192) = 1 := by decide +kernel
  have a24 : coefV1 24 = -1 := by decide +kernel
  have a25 : coefV1 25 = 1 := by decide +kernel
  have a26 : coefV1 26 = 1 := by decide +kernel
  have a27 : coefV1 27 = -1 := by decide +kernel
  have a28 : coefV1 28 = 1 := by decide +kernel
  have a29 : coefV1 29 = -1 := by decide +kernel
  have a30 : coefV1 30 = -1 := by decide +kernel
  have a31 : coefV1 31 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a24, a25, a26, a27, a28, a29, a30, a31]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 1, cell 11 (root face 45) -/

/-- The eight `(f,u)`-chains of the root face of cell `11`. -/
def LP_1_11 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨268⟩, ⟨783⟩), by decide +kernel⟩,
  ⟨(⟨268⟩, ⟨798⟩), by decide +kernel⟩,
  ⟨(⟨272⟩, ⟨747⟩), by decide +kernel⟩,
  ⟨(⟨272⟩, ⟨765⟩), by decide +kernel⟩,
  ⟨(⟨284⟩, ⟨765⟩), by decide +kernel⟩,
  ⟨(⟨284⟩, ⟨798⟩), by decide +kernel⟩,
  ⟨(⟨288⟩, ⟨747⟩), by decide +kernel⟩,
  ⟨(⟨288⟩, ⟨783⟩), by decide +kernel⟩]

theorem LP_1_11_inj : Function.Injective LP_1_11 := by decide +kernel

theorem LP_1_11_surj : Function.Surjective LP_1_11 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨268⟩, ⟨272⟩, ⟨284⟩, ⟨288⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨268⟩ : QbarCW.Cell) = {⟨783⟩, ⟨798⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨272⟩ : QbarCW.Cell) = {⟨747⟩, ⟨765⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨284⟩ : QbarCW.Cell) = {⟨765⟩, ⟨798⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨288⟩ : QbarCW.Cell) = {⟨747⟩, ⟨783⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_1_8 : cChain 1 (slabV 1 (tauV1 8)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_300
      = mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_5_636_300

theorem chC_1_9 : cChain 1 (slabV 1 (tauV1 9)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_300
      = mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_5_654_300

theorem chC_1_10 : cChain 1 (slabV 1 (tauV1 10)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304
      = mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_5_594_304

theorem chC_1_11 : cChain 1 (slabV 1 (tauV1 11)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_304
      = mkSimplex (Mbar.rootCx 2 (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_11 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_5_615_304


end

end Work.BridgeSquare.SlabBuild
