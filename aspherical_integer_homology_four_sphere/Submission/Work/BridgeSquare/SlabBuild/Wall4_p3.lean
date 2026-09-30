import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts4
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p1
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p2

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



theorem LP_4_39_surj : Function.Surjective LP_4_39 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨207⟩, ⟨371⟩, ⟨451⟩, ⟨459⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨207⟩ : QbarCW.Cell) = {⟨807⟩, ⟨830⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨371⟩ : QbarCW.Cell) = {⟨807⟩, ⟨833⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨451⟩ : QbarCW.Cell) = {⟨687⟩, ⟨830⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨459⟩ : QbarCW.Cell) = {⟨687⟩, ⟨833⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_16 : cChain 4 (slabV 4 (tauV4 16)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_18_623_298

theorem chC_4_17 : cChain 4 (slabV 4 (tauV4 17)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_18_635_298

theorem chC_4_18 : cChain 4 (slabV 4 (tauV4 18)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_18_623_350

theorem chC_4_19 : cChain 4 (slabV 4 (tauV4 19)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_18_638_350

theorem chC_4_20 : cChain 4 (slabV 4 (tauV4 20)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_18_629_438

theorem chC_4_21 : cChain 4 (slabV 4 (tauV4 21)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_18_635_438

theorem chC_4_22 : cChain 4 (slabV 4 (tauV4 22)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_18_629_446

theorem chC_4_23 : cChain 4 (slabV 4 (tauV4 23)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_18_638_446

/-- **Wall leaf (cusp 4, cell 39)**: the 8 wall triangles of cell `39` give its `Ψ_M`-image. -/
theorem wallCell_4_39 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 39), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (39 : Fin 192) • (PsiM.f 2) (Pi.single (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 39) = {16, 17, 18, 19, 20, 21, 22, 23} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_39) LP_4_39_inj LP_4_39_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_16, chC_4_17, chC_4_18, chC_4_19, chC_4_20, chC_4_21, chC_4_22, chC_4_23]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 0).1.1.idx) * qInc (LP_4_39 0).1.1.idx (LP_4_39 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 1).1.1.idx) * qInc (LP_4_39 1).1.1.idx (LP_4_39 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 2).1.1.idx) * qInc (LP_4_39 2).1.1.idx (LP_4_39 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 3).1.1.idx) * qInc (LP_4_39 3).1.1.idx (LP_4_39 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 4).1.1.idx) * qInc (LP_4_39 4).1.1.idx (LP_4_39 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 5).1.1.idx) * qInc (LP_4_39 5).1.1.idx (LP_4_39 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 6).1.1.idx) * qInc (LP_4_39 6).1.1.idx (LP_4_39 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 7).1.1.idx) * qInc (LP_4_39 7).1.1.idx (LP_4_39 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (39 : Fin 192) = -1 := by decide +kernel
  have a16 : coefV4 16 = -1 := by decide +kernel
  have a17 : coefV4 17 = 1 := by decide +kernel
  have a18 : coefV4 18 = 1 := by decide +kernel
  have a19 : coefV4 19 = -1 := by decide +kernel
  have a20 : coefV4 20 = 1 := by decide +kernel
  have a21 : coefV4 21 = -1 := by decide +kernel
  have a22 : coefV4 22 = -1 := by decide +kernel
  have a23 : coefV4 23 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a16, a17, a18, a19, a20, a21, a22, a23]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 42 (root face 103) -/

/-- The eight `(f,u)`-chains of the root face of cell `42`. -/
def LP_4_42 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨302⟩, ⟨578⟩), by decide +kernel⟩,
  ⟨(⟨302⟩, ⟨593⟩), by decide +kernel⟩,
  ⟨(⟨398⟩, ⟨578⟩), by decide +kernel⟩,
  ⟨(⟨398⟩, ⟨596⟩), by decide +kernel⟩,
  ⟨(⟨470⟩, ⟨587⟩), by decide +kernel⟩,
  ⟨(⟨470⟩, ⟨593⟩), by decide +kernel⟩,
  ⟨(⟨478⟩, ⟨587⟩), by decide +kernel⟩,
  ⟨(⟨478⟩, ⟨596⟩), by decide +kernel⟩]

theorem LP_4_42_inj : Function.Injective LP_4_42 := by decide +kernel

theorem LP_4_42_surj : Function.Surjective LP_4_42 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨302⟩, ⟨398⟩, ⟨470⟩, ⟨478⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨302⟩ : QbarCW.Cell) = {⟨578⟩, ⟨593⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨398⟩ : QbarCW.Cell) = {⟨578⟩, ⟨596⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨470⟩ : QbarCW.Cell) = {⟨587⟩, ⟨593⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨478⟩ : QbarCW.Cell) = {⟨587⟩, ⟨596⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_120 : cChain 4 (slabV 4 (tauV4 120)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_44_840_203

theorem chC_4_121 : cChain 4 (slabV 4 (tauV4 121)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_44_857_203

theorem chC_4_122 : cChain 4 (slabV 4 (tauV4 122)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_44_840_323

theorem chC_4_123 : cChain 4 (slabV 4 (tauV4 123)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_44_860_323

theorem chC_4_124 : cChain 4 (slabV 4 (tauV4 124)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_44_720_419

theorem chC_4_125 : cChain 4 (slabV 4 (tauV4 125)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_44_857_419

theorem chC_4_126 : cChain 4 (slabV 4 (tauV4 126)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_44_720_427

theorem chC_4_127 : cChain 4 (slabV 4 (tauV4 127)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_44_860_427

/-- **Wall leaf (cusp 4, cell 42)**: the 8 wall triangles of cell `42` give its `Ψ_M`-image. -/
theorem wallCell_4_42 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 42), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (42 : Fin 192) • (PsiM.f 2) (Pi.single (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 42) = {120, 121, 122, 123, 124, 125, 126, 127} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_42) LP_4_42_inj LP_4_42_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_120, chC_4_121, chC_4_122, chC_4_123, chC_4_124, chC_4_125, chC_4_126, chC_4_127]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 0).1.1.idx) * qInc (LP_4_42 0).1.1.idx (LP_4_42 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 1).1.1.idx) * qInc (LP_4_42 1).1.1.idx (LP_4_42 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 2).1.1.idx) * qInc (LP_4_42 2).1.1.idx (LP_4_42 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 3).1.1.idx) * qInc (LP_4_42 3).1.1.idx (LP_4_42 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 4).1.1.idx) * qInc (LP_4_42 4).1.1.idx (LP_4_42 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 5).1.1.idx) * qInc (LP_4_42 5).1.1.idx (LP_4_42 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 6).1.1.idx) * qInc (LP_4_42 6).1.1.idx (LP_4_42 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 7).1.1.idx) * qInc (LP_4_42 7).1.1.idx (LP_4_42 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 4 0 (42 : Fin 192) = -1 := by decide +kernel
  have a120 : coefV4 120 = 1 := by decide +kernel
  have a121 : coefV4 121 = -1 := by decide +kernel
  have a122 : coefV4 122 = -1 := by decide +kernel
  have a123 : coefV4 123 = 1 := by decide +kernel
  have a124 : coefV4 124 = -1 := by decide +kernel
  have a125 : coefV4 125 = 1 := by decide +kernel
  have a126 : coefV4 126 = 1 := by decide +kernel
  have a127 : coefV4 127 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a120, a121, a122, a123, a124, a125, a126, a127]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 43 (root face 104) -/

/-- The eight `(f,u)`-chains of the root face of cell `43`. -/
def LP_4_43 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨303⟩, ⟨579⟩), by decide +kernel⟩,
  ⟨(⟨303⟩, ⟨614⟩), by decide +kernel⟩,
  ⟨(⟨399⟩, ⟨579⟩), by decide +kernel⟩,
  ⟨(⟨399⟩, ⟨617⟩), by decide +kernel⟩,
  ⟨(⟨466⟩, ⟨608⟩), by decide +kernel⟩,
  ⟨(⟨466⟩, ⟨614⟩), by decide +kernel⟩,
  ⟨(⟨474⟩, ⟨608⟩), by decide +kernel⟩,
  ⟨(⟨474⟩, ⟨617⟩), by decide +kernel⟩]

theorem LP_4_43_inj : Function.Injective LP_4_43 := by decide +kernel

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

theorem LP_4_45_surj : Function.Surjective LP_4_45 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨271⟩, ⟨375⟩, ⟨467⟩, ⟨475⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨271⟩ : QbarCW.Cell) = {⟨735⟩, ⟨764⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨375⟩ : QbarCW.Cell) = {⟨735⟩, ⟨767⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨467⟩ : QbarCW.Cell) = {⟨609⟩, ⟨764⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨475⟩ : QbarCW.Cell) = {⟨609⟩, ⟨767⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_64 : cChain 4 (slabV 4 (tauV4 64)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_234
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_701_234

theorem chC_4_65 : cChain 4 (slabV 4 (tauV4 65)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_234
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_710_234

theorem chC_4_66 : cChain 4 (slabV 4 (tauV4 66)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_701_346

theorem chC_4_67 : cChain 4 (slabV 4 (tauV4 67)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_713_346

theorem chC_4_68 : cChain 4 (slabV 4 (tauV4 68)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_704_422

theorem chC_4_69 : cChain 4 (slabV 4 (tauV4 69)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_710_422

theorem chC_4_70 : cChain 4 (slabV 4 (tauV4 70)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_704_430

theorem chC_4_71 : cChain 4 (slabV 4 (tauV4 71)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_713_430

/-- **Wall leaf (cusp 4, cell 45)**: the 8 wall triangles of cell `45` give its `Ψ_M`-image. -/
theorem wallCell_4_45 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 45), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (45 : Fin 192) • (PsiM.f 2) (Pi.single (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 45) = {64, 65, 66, 67, 68, 69, 70, 71} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_45) LP_4_45_inj LP_4_45_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_64, chC_4_65, chC_4_66, chC_4_67, chC_4_68, chC_4_69, chC_4_70, chC_4_71]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 0).1.1.idx) * qInc (LP_4_45 0).1.1.idx (LP_4_45 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 1).1.1.idx) * qInc (LP_4_45 1).1.1.idx (LP_4_45 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 2).1.1.idx) * qInc (LP_4_45 2).1.1.idx (LP_4_45 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 3).1.1.idx) * qInc (LP_4_45 3).1.1.idx (LP_4_45 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 4).1.1.idx) * qInc (LP_4_45 4).1.1.idx (LP_4_45 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 5).1.1.idx) * qInc (LP_4_45 5).1.1.idx (LP_4_45 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 6).1.1.idx) * qInc (LP_4_45 6).1.1.idx (LP_4_45 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 7).1.1.idx) * qInc (LP_4_45 7).1.1.idx (LP_4_45 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (45 : Fin 192) = 1 := by decide +kernel
  have a64 : coefV4 64 = 1 := by decide +kernel
  have a65 : coefV4 65 = -1 := by decide +kernel
  have a66 : coefV4 66 = -1 := by decide +kernel
  have a67 : coefV4 67 = 1 := by decide +kernel
  have a68 : coefV4 68 = -1 := by decide +kernel
  have a69 : coefV4 69 = 1 := by decide +kernel
  have a70 : coefV4 70 = 1 := by decide +kernel
  have a71 : coefV4 71 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a64, a65, a66, a67, a68, a69, a70, a71]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### Assembly for cusp 4 -/

/-- **The wall identification for cusp 4** (untranslated triangles). -/
theorem wallPsi_4 :
    (∑ j : Idx4, coefV4 j • cChain 4 (slabV 4 (tauV4 j))) = (PsiM.f 2) (planeCycleVec 4 0) := by
  have hexp : (planeCycleVec 4 0 : Fin 192 → ℤ)
      = ∑ e ∈ ({24, 25, 26, 27, 30, 31, 32, 33, 36, 37, 38, 39, 42, 43, 44, 45} : Finset (Fin 192)), planeCycleVec 4 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ) := by
    funext i; rw [Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]; revert i; decide +kernel
  have hR : (PsiM.f 2) (planeCycleVec 4 0)
      = ∑ e ∈ ({24, 25, 26, 27, 30, 31, 32, 33, 36, 37, 38, 39, 42, 43, 44, 45} : Finset (Fin 192)), planeCycleVec 4 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
    calc (PsiM.f 2) (planeCycleVec 4 0)
        = (PsiM.f 2) (∑ e ∈ ({24, 25, 26, 27, 30, 31, 32, 33, 36, 37, 38, 39, 42, 43, 44, 45} : Finset (Fin 192)), planeCycleVec 4 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          congrArg (PsiM.f 2) hexp
      _ = ∑ e ∈ ({24, 25, 26, 27, 30, 31, 32, 33, 36, 37, 38, 39, 42, 43, 44, 45} : Finset (Fin 192)), (PsiM.f 2) (planeCycleVec 4 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          map_sum _ _ _
      _ = ∑ e ∈ ({24, 25, 26, 27, 30, 31, 32, 33, 36, 37, 38, 39, 42, 43, 44, 45} : Finset (Fin 192)), planeCycleVec 4 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
          Finset.sum_congr rfl fun e _ => map_zsmul _ _ _
  rw [hR, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := ({24, 25, 26, 27, 30, 31, 32, 33, 36, 37, 38, 39, 42, 43, 44, 45} : Finset (Fin 192))) (g := cellV4)
    (fun j _ => by revert j; decide +kernel)]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact wallCell_4_24
  · exact wallCell_4_25
  · exact wallCell_4_26
  · exact wallCell_4_27
  · exact wallCell_4_30
  · exact wallCell_4_31
  · exact wallCell_4_32
  · exact wallCell_4_33
  · exact wallCell_4_36
  · exact wallCell_4_37
  · exact wallCell_4_38
  · exact wallCell_4_39
  · exact wallCell_4_42
  · exact wallCell_4_43
  · exact wallCell_4_44
  · exact wallCell_4_45

theorem lamV_mem4 (j : Idx4) : slabL 4 (lamV4 j) ∈ Work.Cusp.lattice 4 := by
  have hk1 : Work.Cusp.kv 4 1 ∈ Work.Cusp.lattice 4 := AddSubgroup.subset_closure (Set.mem_range_self 1)
  have hk2 : Work.Cusp.kv 4 2 ∈ Work.Cusp.lattice 4 := AddSubgroup.subset_closure (Set.mem_range_self 2)
  have h : slabL 4 (lamV4 j) ∈ ({0, -Work.Cusp.kv 4 2, -Work.Cusp.kv 4 1, -Work.Cusp.kv 4 1 - Work.Cusp.kv 4 2} : Set CuspE3) := by
    fin_cases j <;> simp [lamV4, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3] <;> abel_nf <;> simp
  rcases h with h | h | h | h <;> rw [h]
  · exact zero_mem _
  · exact neg_mem hk2
  · exact neg_mem hk1
  · exact sub_mem (neg_mem hk1) hk2

/-- **The wall chain of cusp 4 realises `Ψ_M(planeCycleVec 4 0)`** (the `W` of `wall_collar 4`, `s = 1`). -/
theorem wall_slab4 : slabChain 4 2 (wallChain4 : AffC 2) = (PsiM.f 2) (planeCycleVec 4 0) := by
  rw [← wallPsi_4, wallChain4, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, slabChain_single_one]
  have h1 : slabV 4 (fun k => tauV4 j k + lamV4 j) = fun k => slabV 4 (tauV4 j) k + slabL 4 (lamV4 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 4 (slabV 4 (tauV4 j)) (slabL 4 (lamV4 j)) (lamV_mem4 j)]

end

end Work.BridgeSquare.SlabBuild
