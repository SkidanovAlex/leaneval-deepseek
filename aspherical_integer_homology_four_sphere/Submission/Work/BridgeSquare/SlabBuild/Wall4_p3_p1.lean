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


end

end Work.BridgeSquare.SlabBuild
