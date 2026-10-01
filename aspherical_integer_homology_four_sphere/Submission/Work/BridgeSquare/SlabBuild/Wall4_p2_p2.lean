import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts4
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p1
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p2_p1

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



end

end Work.BridgeSquare.SlabBuild
