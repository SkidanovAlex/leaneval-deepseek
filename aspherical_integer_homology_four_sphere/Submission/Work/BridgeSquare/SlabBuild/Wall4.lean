import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts4
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



/-! ### cusp 4, cell 24 (root face 82) -/

/-- The eight `(f,u)`-chains of the root face of cell `24`. -/
def LP_4_24 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨234⟩, ⟨701⟩), by decide⟩,
  ⟨(⟨234⟩, ⟨710⟩), by decide⟩,
  ⟨(⟨346⟩, ⟨701⟩), by decide⟩,
  ⟨(⟨346⟩, ⟨713⟩), by decide⟩,
  ⟨(⟨422⟩, ⟨704⟩), by decide⟩,
  ⟨(⟨422⟩, ⟨710⟩), by decide⟩,
  ⟨(⟨430⟩, ⟨704⟩), by decide⟩,
  ⟨(⟨430⟩, ⟨713⟩), by decide⟩]

theorem LP_4_24_inj : Function.Injective LP_4_24 := by decide

theorem LP_4_24_surj : Function.Surjective LP_4_24 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨234⟩, ⟨346⟩, ⟨422⟩, ⟨430⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨234⟩ : QbarCW.Cell) = {⟨701⟩, ⟨710⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨346⟩ : QbarCW.Cell) = {⟨701⟩, ⟨713⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨422⟩ : QbarCW.Cell) = {⟨704⟩, ⟨710⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨430⟩ : QbarCW.Cell) = {⟨704⟩, ⟨713⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_56 : cChain 4 (slabV 4 (tauV4 56)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_25_735_271

theorem chC_4_57 : cChain 4 (slabV 4 (tauV4 57)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_25_764_271

theorem chC_4_58 : cChain 4 (slabV 4 (tauV4 58)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_25_735_375

theorem chC_4_59 : cChain 4 (slabV 4 (tauV4 59)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_375
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_25_767_375

theorem chC_4_60 : cChain 4 (slabV 4 (tauV4 60)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_467
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_25_609_467

theorem chC_4_61 : cChain 4 (slabV 4 (tauV4 61)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_467
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_25_764_467

theorem chC_4_62 : cChain 4 (slabV 4 (tauV4 62)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_475
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_25_609_475

theorem chC_4_63 : cChain 4 (slabV 4 (tauV4 63)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_475
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_25_767_475

/-- **Wall leaf (cusp 4, cell 24)**: the 8 wall triangles of cell `24` give its `Ψ_M`-image. -/
theorem wallCell_4_24 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 24), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (24 : Fin 192) • (PsiM.f 2) (Pi.single (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 24) = {56, 57, 58, 59, 60, 61, 62, 63} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_24) LP_4_24_inj LP_4_24_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_56, chC_4_57, chC_4_58, chC_4_59, chC_4_60, chC_4_61, chC_4_62, chC_4_63]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 0).1.1.idx) * qInc (LP_4_24 0).1.1.idx (LP_4_24 0).1.2.idx) = -1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 1).1.1.idx) * qInc (LP_4_24 1).1.1.idx (LP_4_24 1).1.2.idx) = 1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 2).1.1.idx) * qInc (LP_4_24 2).1.1.idx (LP_4_24 2).1.2.idx) = 1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 3).1.1.idx) * qInc (LP_4_24 3).1.1.idx (LP_4_24 3).1.2.idx) = -1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 4).1.1.idx) * qInc (LP_4_24 4).1.1.idx (LP_4_24 4).1.2.idx) = 1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 5).1.1.idx) * qInc (LP_4_24 5).1.1.idx (LP_4_24 5).1.2.idx) = -1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 6).1.1.idx) * qInc (LP_4_24 6).1.1.idx (LP_4_24 6).1.2.idx) = -1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 7).1.1.idx) * qInc (LP_4_24 7).1.1.idx (LP_4_24 7).1.2.idx) = 1 := by decide
  have hc : planeCycleVec 4 0 (24 : Fin 192) = -1 := by decide
  have a56 : coefV4 56 = 1 := by decide
  have a57 : coefV4 57 = -1 := by decide
  have a58 : coefV4 58 = -1 := by decide
  have a59 : coefV4 59 = 1 := by decide
  have a60 : coefV4 60 = -1 := by decide
  have a61 : coefV4 61 = 1 := by decide
  have a62 : coefV4 62 = 1 := by decide
  have a63 : coefV4 63 = -1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a56, a57, a58, a59, a60, a61, a62, a63]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 25 (root face 83) -/

/-- The eight `(f,u)`-chains of the root face of cell `25`. -/
def LP_4_25 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨235⟩, ⟨702⟩), by decide⟩,
  ⟨(⟨235⟩, ⟨725⟩), by decide⟩,
  ⟨(⟨347⟩, ⟨702⟩), by decide⟩,
  ⟨(⟨347⟩, ⟨728⟩), by decide⟩,
  ⟨(⟨418⟩, ⟨719⟩), by decide⟩,
  ⟨(⟨418⟩, ⟨725⟩), by decide⟩,
  ⟨(⟨426⟩, ⟨719⟩), by decide⟩,
  ⟨(⟨426⟩, ⟨728⟩), by decide⟩]

theorem LP_4_25_inj : Function.Injective LP_4_25 := by decide

theorem LP_4_25_surj : Function.Surjective LP_4_25 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨235⟩, ⟨347⟩, ⟨418⟩, ⟨426⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨235⟩ : QbarCW.Cell) = {⟨702⟩, ⟨725⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨347⟩ : QbarCW.Cell) = {⟨702⟩, ⟨728⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨418⟩ : QbarCW.Cell) = {⟨719⟩, ⟨725⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨426⟩ : QbarCW.Cell) = {⟨719⟩, ⟨728⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_8 : cChain 4 (slabV 4 (tauV4 8)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_17_734_270

theorem chC_4_9 : cChain 4 (slabV 4 (tauV4 9)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_17_746_270

theorem chC_4_10 : cChain 4 (slabV 4 (tauV4 10)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_17_734_374

theorem chC_4_11 : cChain 4 (slabV 4 (tauV4 11)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_17_749_374

theorem chC_4_12 : cChain 4 (slabV 4 (tauV4 12)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_17_588_471

theorem chC_4_13 : cChain 4 (slabV 4 (tauV4 13)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_17_746_471

theorem chC_4_14 : cChain 4 (slabV 4 (tauV4 14)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_17_588_479

theorem chC_4_15 : cChain 4 (slabV 4 (tauV4 15)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_17_749_479

/-- **Wall leaf (cusp 4, cell 25)**: the 8 wall triangles of cell `25` give its `Ψ_M`-image. -/
theorem wallCell_4_25 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 25), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (25 : Fin 192) • (PsiM.f 2) (Pi.single (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 25) = {8, 9, 10, 11, 12, 13, 14, 15} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_25) LP_4_25_inj LP_4_25_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_8, chC_4_9, chC_4_10, chC_4_11, chC_4_12, chC_4_13, chC_4_14, chC_4_15]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 0).1.1.idx) * qInc (LP_4_25 0).1.1.idx (LP_4_25 0).1.2.idx) = -1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 1).1.1.idx) * qInc (LP_4_25 1).1.1.idx (LP_4_25 1).1.2.idx) = 1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 2).1.1.idx) * qInc (LP_4_25 2).1.1.idx (LP_4_25 2).1.2.idx) = 1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 3).1.1.idx) * qInc (LP_4_25 3).1.1.idx (LP_4_25 3).1.2.idx) = -1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 4).1.1.idx) * qInc (LP_4_25 4).1.1.idx (LP_4_25 4).1.2.idx) = 1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 5).1.1.idx) * qInc (LP_4_25 5).1.1.idx (LP_4_25 5).1.2.idx) = -1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 6).1.1.idx) * qInc (LP_4_25 6).1.1.idx (LP_4_25 6).1.2.idx) = -1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 7).1.1.idx) * qInc (LP_4_25 7).1.1.idx (LP_4_25 7).1.2.idx) = 1 := by decide
  have hc : planeCycleVec 4 0 (25 : Fin 192) = 1 := by decide
  have a8 : coefV4 8 = -1 := by decide
  have a9 : coefV4 9 = 1 := by decide
  have a10 : coefV4 10 = 1 := by decide
  have a11 : coefV4 11 = -1 := by decide
  have a12 : coefV4 12 = 1 := by decide
  have a13 : coefV4 13 = -1 := by decide
  have a14 : coefV4 14 = -1 := by decide
  have a15 : coefV4 15 = 1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a8, a9, a10, a11, a12, a13, a14, a15]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 26 (root face 84) -/

/-- The eight `(f,u)`-chains of the root face of cell `26`. -/
def LP_4_26 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨202⟩, ⟨839⟩), by decide⟩,
  ⟨(⟨202⟩, ⟨845⟩), by decide⟩,
  ⟨(⟨322⟩, ⟨839⟩), by decide⟩,
  ⟨(⟨322⟩, ⟨848⟩), by decide⟩,
  ⟨(⟨423⟩, ⟨705⟩), by decide⟩,
  ⟨(⟨423⟩, ⟨845⟩), by decide⟩,
  ⟨(⟨431⟩, ⟨705⟩), by decide⟩,
  ⟨(⟨431⟩, ⟨848⟩), by decide⟩]

theorem LP_4_26_inj : Function.Injective LP_4_26 := by decide

theorem LP_4_26_surj : Function.Surjective LP_4_26 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨202⟩, ⟨322⟩, ⟨423⟩, ⟨431⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨202⟩ : QbarCW.Cell) = {⟨839⟩, ⟨845⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨322⟩ : QbarCW.Cell) = {⟨839⟩, ⟨848⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨423⟩ : QbarCW.Cell) = {⟨705⟩, ⟨845⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨431⟩ : QbarCW.Cell) = {⟨705⟩, ⟨848⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_32 : cChain 4 (slabV 4 (tauV4 32)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_21_579_303

theorem chC_4_33 : cChain 4 (slabV 4 (tauV4 33)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_21_614_303

theorem chC_4_34 : cChain 4 (slabV 4 (tauV4 34)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_21_579_399

theorem chC_4_35 : cChain 4 (slabV 4 (tauV4 35)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_21_617_399

theorem chC_4_36 : cChain 4 (slabV 4 (tauV4 36)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_21_608_466

theorem chC_4_37 : cChain 4 (slabV 4 (tauV4 37)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_21_614_466

theorem chC_4_38 : cChain 4 (slabV 4 (tauV4 38)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_21_608_474

theorem chC_4_39 : cChain 4 (slabV 4 (tauV4 39)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474
      = mkSimplex (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_26 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_21_617_474

/-- **Wall leaf (cusp 4, cell 26)**: the 8 wall triangles of cell `26` give its `Ψ_M`-image. -/
theorem wallCell_4_26 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 26), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (26 : Fin 192) • (PsiM.f 2) (Pi.single (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 26) = {32, 33, 34, 35, 36, 37, 38, 39} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_26) LP_4_26_inj LP_4_26_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_32, chC_4_33, chC_4_34, chC_4_35, chC_4_36, chC_4_37, chC_4_38, chC_4_39]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 0).1.1.idx) * qInc (LP_4_26 0).1.1.idx (LP_4_26 0).1.2.idx) = 1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 1).1.1.idx) * qInc (LP_4_26 1).1.1.idx (LP_4_26 1).1.2.idx) = -1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 2).1.1.idx) * qInc (LP_4_26 2).1.1.idx (LP_4_26 2).1.2.idx) = -1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 3).1.1.idx) * qInc (LP_4_26 3).1.1.idx (LP_4_26 3).1.2.idx) = 1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 4).1.1.idx) * qInc (LP_4_26 4).1.1.idx (LP_4_26 4).1.2.idx) = -1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 5).1.1.idx) * qInc (LP_4_26 5).1.1.idx (LP_4_26 5).1.2.idx) = 1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 6).1.1.idx) * qInc (LP_4_26 6).1.1.idx (LP_4_26 6).1.2.idx) = 1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_26 7).1.1.idx) * qInc (LP_4_26 7).1.1.idx (LP_4_26 7).1.2.idx) = -1 := by decide
  have hc : planeCycleVec 4 0 (26 : Fin 192) = -1 := by decide
  have a32 : coefV4 32 = -1 := by decide
  have a33 : coefV4 33 = 1 := by decide
  have a34 : coefV4 34 = 1 := by decide
  have a35 : coefV4 35 = -1 := by decide
  have a36 : coefV4 36 = 1 := by decide
  have a37 : coefV4 37 = -1 := by decide
  have a38 : coefV4 38 = -1 := by decide
  have a39 : coefV4 39 = 1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a32, a33, a34, a35, a36, a37, a38, a39]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 27 (root face 85) -/

/-- The eight `(f,u)`-chains of the root face of cell `27`. -/
def LP_4_27 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨203⟩, ⟨840⟩), by decide⟩,
  ⟨(⟨203⟩, ⟨857⟩), by decide⟩,
  ⟨(⟨323⟩, ⟨840⟩), by decide⟩,
  ⟨(⟨323⟩, ⟨860⟩), by decide⟩,
  ⟨(⟨419⟩, ⟨720⟩), by decide⟩,
  ⟨(⟨419⟩, ⟨857⟩), by decide⟩,
  ⟨(⟨427⟩, ⟨720⟩), by decide⟩,
  ⟨(⟨427⟩, ⟨860⟩), by decide⟩]

theorem LP_4_27_inj : Function.Injective LP_4_27 := by decide

theorem LP_4_27_surj : Function.Surjective LP_4_27 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨203⟩, ⟨323⟩, ⟨419⟩, ⟨427⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨203⟩ : QbarCW.Cell) = {⟨840⟩, ⟨857⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨323⟩ : QbarCW.Cell) = {⟨840⟩, ⟨860⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨419⟩ : QbarCW.Cell) = {⟨720⟩, ⟨857⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨427⟩ : QbarCW.Cell) = {⟨720⟩, ⟨860⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_0 : cChain 4 (slabV 4 (tauV4 0)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_16_578_302

theorem chC_4_1 : cChain 4 (slabV 4 (tauV4 1)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_16_593_302

theorem chC_4_2 : cChain 4 (slabV 4 (tauV4 2)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_16_578_398

theorem chC_4_3 : cChain 4 (slabV 4 (tauV4 3)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_16_596_398

theorem chC_4_4 : cChain 4 (slabV 4 (tauV4 4)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_16_587_470

theorem chC_4_5 : cChain 4 (slabV 4 (tauV4 5)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_16_593_470

theorem chC_4_6 : cChain 4 (slabV 4 (tauV4 6)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_16_587_478

theorem chC_4_7 : cChain 4 (slabV 4 (tauV4 7)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478
      = mkSimplex (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_27 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_16_596_478

/-- **Wall leaf (cusp 4, cell 27)**: the 8 wall triangles of cell `27` give its `Ψ_M`-image. -/
theorem wallCell_4_27 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 27), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (27 : Fin 192) • (PsiM.f 2) (Pi.single (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 27) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_27) LP_4_27_inj LP_4_27_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_0, chC_4_1, chC_4_2, chC_4_3, chC_4_4, chC_4_5, chC_4_6, chC_4_7]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 0).1.1.idx) * qInc (LP_4_27 0).1.1.idx (LP_4_27 0).1.2.idx) = 1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 1).1.1.idx) * qInc (LP_4_27 1).1.1.idx (LP_4_27 1).1.2.idx) = -1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 2).1.1.idx) * qInc (LP_4_27 2).1.1.idx (LP_4_27 2).1.2.idx) = -1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 3).1.1.idx) * qInc (LP_4_27 3).1.1.idx (LP_4_27 3).1.2.idx) = 1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 4).1.1.idx) * qInc (LP_4_27 4).1.1.idx (LP_4_27 4).1.2.idx) = -1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 5).1.1.idx) * qInc (LP_4_27 5).1.1.idx (LP_4_27 5).1.2.idx) = 1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 6).1.1.idx) * qInc (LP_4_27 6).1.1.idx (LP_4_27 6).1.2.idx) = 1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_27 7).1.1.idx) * qInc (LP_4_27 7).1.1.idx (LP_4_27 7).1.2.idx) = -1 := by decide
  have hc : planeCycleVec 4 0 (27 : Fin 192) = 1 := by decide
  have a0 : coefV4 0 = 1 := by decide
  have a1 : coefV4 1 = -1 := by decide
  have a2 : coefV4 2 = -1 := by decide
  have a3 : coefV4 3 = 1 := by decide
  have a4 : coefV4 4 = -1 := by decide
  have a5 : coefV4 5 = 1 := by decide
  have a6 : coefV4 6 = 1 := by decide
  have a7 : coefV4 7 = -1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a0, a1, a2, a3, a4, a5, a6, a7]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 30 (root face 89) -/

/-- The eight `(f,u)`-chains of the root face of cell `30`. -/
def LP_4_30 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨298⟩, ⟨623⟩), by decide⟩,
  ⟨(⟨298⟩, ⟨635⟩), by decide⟩,
  ⟨(⟨350⟩, ⟨623⟩), by decide⟩,
  ⟨(⟨350⟩, ⟨638⟩), by decide⟩,
  ⟨(⟨438⟩, ⟨629⟩), by decide⟩,
  ⟨(⟨438⟩, ⟨635⟩), by decide⟩,
  ⟨(⟨446⟩, ⟨629⟩), by decide⟩,
  ⟨(⟨446⟩, ⟨638⟩), by decide⟩]

theorem LP_4_30_inj : Function.Injective LP_4_30 := by decide

theorem LP_4_30_surj : Function.Surjective LP_4_30 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨298⟩, ⟨350⟩, ⟨438⟩, ⟨446⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨298⟩ : QbarCW.Cell) = {⟨623⟩, ⟨635⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨350⟩ : QbarCW.Cell) = {⟨623⟩, ⟨638⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨438⟩ : QbarCW.Cell) = {⟨629⟩, ⟨635⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨446⟩ : QbarCW.Cell) = {⟨629⟩, ⟨638⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_104 : cChain 4 (slabV 4 (tauV4 104)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_37_807_207

theorem chC_4_105 : cChain 4 (slabV 4 (tauV4 105)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_37_830_207

theorem chC_4_106 : cChain 4 (slabV 4 (tauV4 106)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_37_807_371

theorem chC_4_107 : cChain 4 (slabV 4 (tauV4 107)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_37_833_371

theorem chC_4_108 : cChain 4 (slabV 4 (tauV4 108)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_37_687_451

theorem chC_4_109 : cChain 4 (slabV 4 (tauV4 109)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_37_830_451

theorem chC_4_110 : cChain 4 (slabV 4 (tauV4 110)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_37_687_459

theorem chC_4_111 : cChain 4 (slabV 4 (tauV4 111)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_37_833_459

/-- **Wall leaf (cusp 4, cell 30)**: the 8 wall triangles of cell `30` give its `Ψ_M`-image. -/
theorem wallCell_4_30 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 30), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (30 : Fin 192) • (PsiM.f 2) (Pi.single (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 30) = {104, 105, 106, 107, 108, 109, 110, 111} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_30) LP_4_30_inj LP_4_30_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_104, chC_4_105, chC_4_106, chC_4_107, chC_4_108, chC_4_109, chC_4_110, chC_4_111]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 0).1.1.idx) * qInc (LP_4_30 0).1.1.idx (LP_4_30 0).1.2.idx) = -1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 1).1.1.idx) * qInc (LP_4_30 1).1.1.idx (LP_4_30 1).1.2.idx) = 1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 2).1.1.idx) * qInc (LP_4_30 2).1.1.idx (LP_4_30 2).1.2.idx) = 1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 3).1.1.idx) * qInc (LP_4_30 3).1.1.idx (LP_4_30 3).1.2.idx) = -1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 4).1.1.idx) * qInc (LP_4_30 4).1.1.idx (LP_4_30 4).1.2.idx) = 1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 5).1.1.idx) * qInc (LP_4_30 5).1.1.idx (LP_4_30 5).1.2.idx) = -1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 6).1.1.idx) * qInc (LP_4_30 6).1.1.idx (LP_4_30 6).1.2.idx) = -1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 7).1.1.idx) * qInc (LP_4_30 7).1.1.idx (LP_4_30 7).1.2.idx) = 1 := by decide
  have hc : planeCycleVec 4 0 (30 : Fin 192) = 1 := by decide
  have a104 : coefV4 104 = -1 := by decide
  have a105 : coefV4 105 = 1 := by decide
  have a106 : coefV4 106 = 1 := by decide
  have a107 : coefV4 107 = -1 := by decide
  have a108 : coefV4 108 = 1 := by decide
  have a109 : coefV4 109 = -1 := by decide
  have a110 : coefV4 110 = -1 := by decide
  have a111 : coefV4 111 = 1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a104, a105, a106, a107, a108, a109, a110, a111]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 31 (root face 90) -/

/-- The eight `(f,u)`-chains of the root face of cell `31`. -/
def LP_4_31 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨299⟩, ⟨624⟩), by decide⟩,
  ⟨(⟨299⟩, ⟨653⟩), by decide⟩,
  ⟨(⟨351⟩, ⟨624⟩), by decide⟩,
  ⟨(⟨351⟩, ⟨656⟩), by decide⟩,
  ⟨(⟨434⟩, ⟨647⟩), by decide⟩,
  ⟨(⟨434⟩, ⟨653⟩), by decide⟩,
  ⟨(⟨442⟩, ⟨647⟩), by decide⟩,
  ⟨(⟨442⟩, ⟨656⟩), by decide⟩]

theorem LP_4_31_inj : Function.Injective LP_4_31 := by decide

theorem LP_4_31_surj : Function.Surjective LP_4_31 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨299⟩, ⟨351⟩, ⟨434⟩, ⟨442⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨299⟩ : QbarCW.Cell) = {⟨624⟩, ⟨653⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨351⟩ : QbarCW.Cell) = {⟨624⟩, ⟨656⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨434⟩ : QbarCW.Cell) = {⟨647⟩, ⟨653⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨442⟩ : QbarCW.Cell) = {⟨647⟩, ⟨656⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_48 : cChain 4 (slabV 4 (tauV4 48)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_206
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_24_806_206

theorem chC_4_49 : cChain 4 (slabV 4 (tauV4 49)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_206
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_24_815_206

theorem chC_4_50 : cChain 4 (slabV 4 (tauV4 50)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_370
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_24_806_370

theorem chC_4_51 : cChain 4 (slabV 4 (tauV4 51)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_370
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_24_818_370

theorem chC_4_52 : cChain 4 (slabV 4 (tauV4 52)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_455
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_24_669_455

theorem chC_4_53 : cChain 4 (slabV 4 (tauV4 53)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_455
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_24_815_455

theorem chC_4_54 : cChain 4 (slabV 4 (tauV4 54)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_24_669_463

theorem chC_4_55 : cChain 4 (slabV 4 (tauV4 55)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_24_818_463

/-- **Wall leaf (cusp 4, cell 31)**: the 8 wall triangles of cell `31` give its `Ψ_M`-image. -/
theorem wallCell_4_31 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 31), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (31 : Fin 192) • (PsiM.f 2) (Pi.single (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 31) = {48, 49, 50, 51, 52, 53, 54, 55} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_31) LP_4_31_inj LP_4_31_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_48, chC_4_49, chC_4_50, chC_4_51, chC_4_52, chC_4_53, chC_4_54, chC_4_55]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 0).1.1.idx) * qInc (LP_4_31 0).1.1.idx (LP_4_31 0).1.2.idx) = -1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 1).1.1.idx) * qInc (LP_4_31 1).1.1.idx (LP_4_31 1).1.2.idx) = 1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 2).1.1.idx) * qInc (LP_4_31 2).1.1.idx (LP_4_31 2).1.2.idx) = 1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 3).1.1.idx) * qInc (LP_4_31 3).1.1.idx (LP_4_31 3).1.2.idx) = -1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 4).1.1.idx) * qInc (LP_4_31 4).1.1.idx (LP_4_31 4).1.2.idx) = 1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 5).1.1.idx) * qInc (LP_4_31 5).1.1.idx (LP_4_31 5).1.2.idx) = -1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 6).1.1.idx) * qInc (LP_4_31 6).1.1.idx (LP_4_31 6).1.2.idx) = -1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_31 7).1.1.idx) * qInc (LP_4_31 7).1.1.idx (LP_4_31 7).1.2.idx) = 1 := by decide
  have hc : planeCycleVec 4 0 (31 : Fin 192) = -1 := by decide
  have a48 : coefV4 48 = 1 := by decide
  have a49 : coefV4 49 = -1 := by decide
  have a50 : coefV4 50 = -1 := by decide
  have a51 : coefV4 51 = 1 := by decide
  have a52 : coefV4 52 = -1 := by decide
  have a53 : coefV4 53 = 1 := by decide
  have a54 : coefV4 54 = 1 := by decide
  have a55 : coefV4 55 = -1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a48, a49, a50, a51, a52, a53, a54, a55]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 32 (root face 91) -/

/-- The eight `(f,u)`-chains of the root face of cell `32`. -/
def LP_4_32 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨266⟩, ⟨773⟩), by decide⟩,
  ⟨(⟨266⟩, ⟨782⟩), by decide⟩,
  ⟨(⟨326⟩, ⟨773⟩), by decide⟩,
  ⟨(⟨326⟩, ⟨785⟩), by decide⟩,
  ⟨(⟨439⟩, ⟨630⟩), by decide⟩,
  ⟨(⟨439⟩, ⟨782⟩), by decide⟩,
  ⟨(⟨447⟩, ⟨630⟩), by decide⟩,
  ⟨(⟨447⟩, ⟨785⟩), by decide⟩]

theorem LP_4_32_inj : Function.Injective LP_4_32 := by decide

theorem LP_4_32_surj : Function.Surjective LP_4_32 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨266⟩, ⟨326⟩, ⟨439⟩, ⟨447⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨266⟩ : QbarCW.Cell) = {⟨773⟩, ⟨782⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨326⟩ : QbarCW.Cell) = {⟨773⟩, ⟨785⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨439⟩ : QbarCW.Cell) = {⟨630⟩, ⟨782⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨447⟩ : QbarCW.Cell) = {⟨630⟩, ⟨785⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_80 : cChain 4 (slabV 4 (tauV4 80)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_31_663_239

theorem chC_4_81 : cChain 4 (slabV 4 (tauV4 81)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_31_692_239

theorem chC_4_82 : cChain 4 (slabV 4 (tauV4 82)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_31_663_395

theorem chC_4_83 : cChain 4 (slabV 4 (tauV4 83)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_31_695_395

theorem chC_4_84 : cChain 4 (slabV 4 (tauV4 84)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_31_686_450

theorem chC_4_85 : cChain 4 (slabV 4 (tauV4 85)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_31_692_450

theorem chC_4_86 : cChain 4 (slabV 4 (tauV4 86)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_31_686_458

theorem chC_4_87 : cChain 4 (slabV 4 (tauV4 87)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458
      = mkSimplex (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_32 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_31_695_458

/-- **Wall leaf (cusp 4, cell 32)**: the 8 wall triangles of cell `32` give its `Ψ_M`-image. -/
theorem wallCell_4_32 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 32), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (32 : Fin 192) • (PsiM.f 2) (Pi.single (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 32) = {80, 81, 82, 83, 84, 85, 86, 87} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_32) LP_4_32_inj LP_4_32_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_80, chC_4_81, chC_4_82, chC_4_83, chC_4_84, chC_4_85, chC_4_86, chC_4_87]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 0).1.1.idx) * qInc (LP_4_32 0).1.1.idx (LP_4_32 0).1.2.idx) = 1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 1).1.1.idx) * qInc (LP_4_32 1).1.1.idx (LP_4_32 1).1.2.idx) = -1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 2).1.1.idx) * qInc (LP_4_32 2).1.1.idx (LP_4_32 2).1.2.idx) = -1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 3).1.1.idx) * qInc (LP_4_32 3).1.1.idx (LP_4_32 3).1.2.idx) = 1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 4).1.1.idx) * qInc (LP_4_32 4).1.1.idx (LP_4_32 4).1.2.idx) = -1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 5).1.1.idx) * qInc (LP_4_32 5).1.1.idx (LP_4_32 5).1.2.idx) = 1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 6).1.1.idx) * qInc (LP_4_32 6).1.1.idx (LP_4_32 6).1.2.idx) = 1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_32 7).1.1.idx) * qInc (LP_4_32 7).1.1.idx (LP_4_32 7).1.2.idx) = -1 := by decide
  have hc : planeCycleVec 4 0 (32 : Fin 192) = 1 := by decide
  have a80 : coefV4 80 = 1 := by decide
  have a81 : coefV4 81 = -1 := by decide
  have a82 : coefV4 82 = -1 := by decide
  have a83 : coefV4 83 = 1 := by decide
  have a84 : coefV4 84 = -1 := by decide
  have a85 : coefV4 85 = 1 := by decide
  have a86 : coefV4 86 = 1 := by decide
  have a87 : coefV4 87 = -1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a80, a81, a82, a83, a84, a85, a86, a87]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 33 (root face 92) -/

/-- The eight `(f,u)`-chains of the root face of cell `33`. -/
def LP_4_33 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨267⟩, ⟨774⟩), by decide⟩,
  ⟨(⟨267⟩, ⟨797⟩), by decide⟩,
  ⟨(⟨327⟩, ⟨774⟩), by decide⟩,
  ⟨(⟨327⟩, ⟨800⟩), by decide⟩,
  ⟨(⟨435⟩, ⟨648⟩), by decide⟩,
  ⟨(⟨435⟩, ⟨797⟩), by decide⟩,
  ⟨(⟨443⟩, ⟨648⟩), by decide⟩,
  ⟨(⟨443⟩, ⟨800⟩), by decide⟩]

theorem LP_4_33_inj : Function.Injective LP_4_33 := by decide

theorem LP_4_33_surj : Function.Surjective LP_4_33 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨267⟩, ⟨327⟩, ⟨435⟩, ⟨443⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨267⟩ : QbarCW.Cell) = {⟨774⟩, ⟨797⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨327⟩ : QbarCW.Cell) = {⟨774⟩, ⟨800⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨435⟩ : QbarCW.Cell) = {⟨648⟩, ⟨797⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨443⟩ : QbarCW.Cell) = {⟨648⟩, ⟨800⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_24 : cChain 4 (slabV 4 (tauV4 24)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_20_662_238

theorem chC_4_25 : cChain 4 (slabV 4 (tauV4 25)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_20_674_238

theorem chC_4_26 : cChain 4 (slabV 4 (tauV4 26)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_20_662_394

theorem chC_4_27 : cChain 4 (slabV 4 (tauV4 27)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_20_677_394

theorem chC_4_28 : cChain 4 (slabV 4 (tauV4 28)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_20_668_454

theorem chC_4_29 : cChain 4 (slabV 4 (tauV4 29)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_20_674_454

theorem chC_4_30 : cChain 4 (slabV 4 (tauV4 30)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_20_668_462

theorem chC_4_31 : cChain 4 (slabV 4 (tauV4 31)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462
      = mkSimplex (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_33 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_20_677_462

/-- **Wall leaf (cusp 4, cell 33)**: the 8 wall triangles of cell `33` give its `Ψ_M`-image. -/
theorem wallCell_4_33 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 33), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (33 : Fin 192) • (PsiM.f 2) (Pi.single (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 33) = {24, 25, 26, 27, 28, 29, 30, 31} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_33) LP_4_33_inj LP_4_33_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_24, chC_4_25, chC_4_26, chC_4_27, chC_4_28, chC_4_29, chC_4_30, chC_4_31]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 0).1.1.idx) * qInc (LP_4_33 0).1.1.idx (LP_4_33 0).1.2.idx) = 1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 1).1.1.idx) * qInc (LP_4_33 1).1.1.idx (LP_4_33 1).1.2.idx) = -1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 2).1.1.idx) * qInc (LP_4_33 2).1.1.idx (LP_4_33 2).1.2.idx) = -1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 3).1.1.idx) * qInc (LP_4_33 3).1.1.idx (LP_4_33 3).1.2.idx) = 1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 4).1.1.idx) * qInc (LP_4_33 4).1.1.idx (LP_4_33 4).1.2.idx) = -1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 5).1.1.idx) * qInc (LP_4_33 5).1.1.idx (LP_4_33 5).1.2.idx) = 1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 6).1.1.idx) * qInc (LP_4_33 6).1.1.idx (LP_4_33 6).1.2.idx) = 1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_33 7).1.1.idx) * qInc (LP_4_33 7).1.1.idx (LP_4_33 7).1.2.idx) = -1 := by decide
  have hc : planeCycleVec 4 0 (33 : Fin 192) = -1 := by decide
  have a24 : coefV4 24 = -1 := by decide
  have a25 : coefV4 25 = 1 := by decide
  have a26 : coefV4 26 = 1 := by decide
  have a27 : coefV4 27 = -1 := by decide
  have a28 : coefV4 28 = 1 := by decide
  have a29 : coefV4 29 = -1 := by decide
  have a30 : coefV4 30 = -1 := by decide
  have a31 : coefV4 31 = 1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a24, a25, a26, a27, a28, a29, a30, a31]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 36 (root face 96) -/

/-- The eight `(f,u)`-chains of the root face of cell `36`. -/
def LP_4_36 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨238⟩, ⟨662⟩), by decide⟩,
  ⟨(⟨238⟩, ⟨674⟩), by decide⟩,
  ⟨(⟨394⟩, ⟨662⟩), by decide⟩,
  ⟨(⟨394⟩, ⟨677⟩), by decide⟩,
  ⟨(⟨454⟩, ⟨668⟩), by decide⟩,
  ⟨(⟨454⟩, ⟨674⟩), by decide⟩,
  ⟨(⟨462⟩, ⟨668⟩), by decide⟩,
  ⟨(⟨462⟩, ⟨677⟩), by decide⟩]

theorem LP_4_36_inj : Function.Injective LP_4_36 := by decide

theorem LP_4_36_surj : Function.Surjective LP_4_36 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨238⟩, ⟨394⟩, ⟨454⟩, ⟨462⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨238⟩ : QbarCW.Cell) = {⟨662⟩, ⟨674⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨394⟩ : QbarCW.Cell) = {⟨662⟩, ⟨677⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨454⟩ : QbarCW.Cell) = {⟨668⟩, ⟨674⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨462⟩ : QbarCW.Cell) = {⟨668⟩, ⟨677⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_96 : cChain 4 (slabV 4 (tauV4 96)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_34_774_267

theorem chC_4_97 : cChain 4 (slabV 4 (tauV4 97)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_34_797_267

theorem chC_4_98 : cChain 4 (slabV 4 (tauV4 98)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_34_774_327

theorem chC_4_99 : cChain 4 (slabV 4 (tauV4 99)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_34_800_327

theorem chC_4_100 : cChain 4 (slabV 4 (tauV4 100)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_34_648_435

theorem chC_4_101 : cChain 4 (slabV 4 (tauV4 101)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_34_797_435

theorem chC_4_102 : cChain 4 (slabV 4 (tauV4 102)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_34_648_443

theorem chC_4_103 : cChain 4 (slabV 4 (tauV4 103)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443
      = mkSimplex (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_36 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_34_800_443

/-- **Wall leaf (cusp 4, cell 36)**: the 8 wall triangles of cell `36` give its `Ψ_M`-image. -/
theorem wallCell_4_36 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 36), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (36 : Fin 192) • (PsiM.f 2) (Pi.single (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 36) = {96, 97, 98, 99, 100, 101, 102, 103} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_36) LP_4_36_inj LP_4_36_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_96, chC_4_97, chC_4_98, chC_4_99, chC_4_100, chC_4_101, chC_4_102, chC_4_103]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 0).1.1.idx) * qInc (LP_4_36 0).1.1.idx (LP_4_36 0).1.2.idx) = -1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 1).1.1.idx) * qInc (LP_4_36 1).1.1.idx (LP_4_36 1).1.2.idx) = 1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 2).1.1.idx) * qInc (LP_4_36 2).1.1.idx (LP_4_36 2).1.2.idx) = 1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 3).1.1.idx) * qInc (LP_4_36 3).1.1.idx (LP_4_36 3).1.2.idx) = -1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 4).1.1.idx) * qInc (LP_4_36 4).1.1.idx (LP_4_36 4).1.2.idx) = 1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 5).1.1.idx) * qInc (LP_4_36 5).1.1.idx (LP_4_36 5).1.2.idx) = -1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 6).1.1.idx) * qInc (LP_4_36 6).1.1.idx (LP_4_36 6).1.2.idx) = -1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_36 7).1.1.idx) * qInc (LP_4_36 7).1.1.idx (LP_4_36 7).1.2.idx) = 1 := by decide
  have hc : planeCycleVec 4 0 (36 : Fin 192) = 1 := by decide
  have a96 : coefV4 96 = -1 := by decide
  have a97 : coefV4 97 = 1 := by decide
  have a98 : coefV4 98 = 1 := by decide
  have a99 : coefV4 99 = -1 := by decide
  have a100 : coefV4 100 = 1 := by decide
  have a101 : coefV4 101 = -1 := by decide
  have a102 : coefV4 102 = -1 := by decide
  have a103 : coefV4 103 = 1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a96, a97, a98, a99, a100, a101, a102, a103]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 37 (root face 97) -/

/-- The eight `(f,u)`-chains of the root face of cell `37`. -/
def LP_4_37 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨239⟩, ⟨663⟩), by decide⟩,
  ⟨(⟨239⟩, ⟨692⟩), by decide⟩,
  ⟨(⟨395⟩, ⟨663⟩), by decide⟩,
  ⟨(⟨395⟩, ⟨695⟩), by decide⟩,
  ⟨(⟨450⟩, ⟨686⟩), by decide⟩,
  ⟨(⟨450⟩, ⟨692⟩), by decide⟩,
  ⟨(⟨458⟩, ⟨686⟩), by decide⟩,
  ⟨(⟨458⟩, ⟨695⟩), by decide⟩]

theorem LP_4_37_inj : Function.Injective LP_4_37 := by decide

theorem LP_4_37_surj : Function.Surjective LP_4_37 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨239⟩, ⟨395⟩, ⟨450⟩, ⟨458⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨239⟩ : QbarCW.Cell) = {⟨663⟩, ⟨692⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨395⟩ : QbarCW.Cell) = {⟨663⟩, ⟨695⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨450⟩ : QbarCW.Cell) = {⟨686⟩, ⟨692⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨458⟩ : QbarCW.Cell) = {⟨686⟩, ⟨695⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_40 : cChain 4 (slabV 4 (tauV4 40)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_22_773_266

theorem chC_4_41 : cChain 4 (slabV 4 (tauV4 41)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_22_782_266

theorem chC_4_42 : cChain 4 (slabV 4 (tauV4 42)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_22_773_326

theorem chC_4_43 : cChain 4 (slabV 4 (tauV4 43)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_22_785_326

theorem chC_4_44 : cChain 4 (slabV 4 (tauV4 44)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_439
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_22_630_439

theorem chC_4_45 : cChain 4 (slabV 4 (tauV4 45)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_439
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_22_782_439

theorem chC_4_46 : cChain 4 (slabV 4 (tauV4 46)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_447
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_22_630_447

theorem chC_4_47 : cChain 4 (slabV 4 (tauV4 47)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_447
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_22_785_447

/-- **Wall leaf (cusp 4, cell 37)**: the 8 wall triangles of cell `37` give its `Ψ_M`-image. -/
theorem wallCell_4_37 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 37), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (37 : Fin 192) • (PsiM.f 2) (Pi.single (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 37) = {40, 41, 42, 43, 44, 45, 46, 47} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_37) LP_4_37_inj LP_4_37_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_40, chC_4_41, chC_4_42, chC_4_43, chC_4_44, chC_4_45, chC_4_46, chC_4_47]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 0).1.1.idx) * qInc (LP_4_37 0).1.1.idx (LP_4_37 0).1.2.idx) = -1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 1).1.1.idx) * qInc (LP_4_37 1).1.1.idx (LP_4_37 1).1.2.idx) = 1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 2).1.1.idx) * qInc (LP_4_37 2).1.1.idx (LP_4_37 2).1.2.idx) = 1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 3).1.1.idx) * qInc (LP_4_37 3).1.1.idx (LP_4_37 3).1.2.idx) = -1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 4).1.1.idx) * qInc (LP_4_37 4).1.1.idx (LP_4_37 4).1.2.idx) = 1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 5).1.1.idx) * qInc (LP_4_37 5).1.1.idx (LP_4_37 5).1.2.idx) = -1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 6).1.1.idx) * qInc (LP_4_37 6).1.1.idx (LP_4_37 6).1.2.idx) = -1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 7).1.1.idx) * qInc (LP_4_37 7).1.1.idx (LP_4_37 7).1.2.idx) = 1 := by decide
  have hc : planeCycleVec 4 0 (37 : Fin 192) = -1 := by decide
  have a40 : coefV4 40 = 1 := by decide
  have a41 : coefV4 41 = -1 := by decide
  have a42 : coefV4 42 = -1 := by decide
  have a43 : coefV4 43 = 1 := by decide
  have a44 : coefV4 44 = -1 := by decide
  have a45 : coefV4 45 = 1 := by decide
  have a46 : coefV4 46 = 1 := by decide
  have a47 : coefV4 47 = -1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a40, a41, a42, a43, a44, a45, a46, a47]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 38 (root face 98) -/

/-- The eight `(f,u)`-chains of the root face of cell `38`. -/
def LP_4_38 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨206⟩, ⟨806⟩), by decide⟩,
  ⟨(⟨206⟩, ⟨815⟩), by decide⟩,
  ⟨(⟨370⟩, ⟨806⟩), by decide⟩,
  ⟨(⟨370⟩, ⟨818⟩), by decide⟩,
  ⟨(⟨455⟩, ⟨669⟩), by decide⟩,
  ⟨(⟨455⟩, ⟨815⟩), by decide⟩,
  ⟨(⟨463⟩, ⟨669⟩), by decide⟩,
  ⟨(⟨463⟩, ⟨818⟩), by decide⟩]

theorem LP_4_38_inj : Function.Injective LP_4_38 := by decide

theorem LP_4_38_surj : Function.Surjective LP_4_38 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨206⟩, ⟨370⟩, ⟨455⟩, ⟨463⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨206⟩ : QbarCW.Cell) = {⟨806⟩, ⟨815⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨370⟩ : QbarCW.Cell) = {⟨806⟩, ⟨818⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨455⟩ : QbarCW.Cell) = {⟨669⟩, ⟨815⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨463⟩ : QbarCW.Cell) = {⟨669⟩, ⟨818⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_72 : cChain 4 (slabV 4 (tauV4 72)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_28_624_299

theorem chC_4_73 : cChain 4 (slabV 4 (tauV4 73)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_28_653_299

theorem chC_4_74 : cChain 4 (slabV 4 (tauV4 74)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_28_624_351

theorem chC_4_75 : cChain 4 (slabV 4 (tauV4 75)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_28_656_351

theorem chC_4_76 : cChain 4 (slabV 4 (tauV4 76)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_28_647_434

theorem chC_4_77 : cChain 4 (slabV 4 (tauV4 77)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_28_653_434

theorem chC_4_78 : cChain 4 (slabV 4 (tauV4 78)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_28_647_442

theorem chC_4_79 : cChain 4 (slabV 4 (tauV4 79)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_28_656_442

/-- **Wall leaf (cusp 4, cell 38)**: the 8 wall triangles of cell `38` give its `Ψ_M`-image. -/
theorem wallCell_4_38 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 38), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (38 : Fin 192) • (PsiM.f 2) (Pi.single (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 38) = {72, 73, 74, 75, 76, 77, 78, 79} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_38) LP_4_38_inj LP_4_38_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_72, chC_4_73, chC_4_74, chC_4_75, chC_4_76, chC_4_77, chC_4_78, chC_4_79]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 0).1.1.idx) * qInc (LP_4_38 0).1.1.idx (LP_4_38 0).1.2.idx) = 1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 1).1.1.idx) * qInc (LP_4_38 1).1.1.idx (LP_4_38 1).1.2.idx) = -1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 2).1.1.idx) * qInc (LP_4_38 2).1.1.idx (LP_4_38 2).1.2.idx) = -1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 3).1.1.idx) * qInc (LP_4_38 3).1.1.idx (LP_4_38 3).1.2.idx) = 1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 4).1.1.idx) * qInc (LP_4_38 4).1.1.idx (LP_4_38 4).1.2.idx) = -1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 5).1.1.idx) * qInc (LP_4_38 5).1.1.idx (LP_4_38 5).1.2.idx) = 1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 6).1.1.idx) * qInc (LP_4_38 6).1.1.idx (LP_4_38 6).1.2.idx) = 1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 7).1.1.idx) * qInc (LP_4_38 7).1.1.idx (LP_4_38 7).1.2.idx) = -1 := by decide
  have hc : planeCycleVec 4 0 (38 : Fin 192) = 1 := by decide
  have a72 : coefV4 72 = 1 := by decide
  have a73 : coefV4 73 = -1 := by decide
  have a74 : coefV4 74 = -1 := by decide
  have a75 : coefV4 75 = 1 := by decide
  have a76 : coefV4 76 = -1 := by decide
  have a77 : coefV4 77 = 1 := by decide
  have a78 : coefV4 78 = 1 := by decide
  have a79 : coefV4 79 = -1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a72, a73, a74, a75, a76, a77, a78, a79]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 39 (root face 99) -/

/-- The eight `(f,u)`-chains of the root face of cell `39`. -/
def LP_4_39 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨207⟩, ⟨807⟩), by decide⟩,
  ⟨(⟨207⟩, ⟨830⟩), by decide⟩,
  ⟨(⟨371⟩, ⟨807⟩), by decide⟩,
  ⟨(⟨371⟩, ⟨833⟩), by decide⟩,
  ⟨(⟨451⟩, ⟨687⟩), by decide⟩,
  ⟨(⟨451⟩, ⟨830⟩), by decide⟩,
  ⟨(⟨459⟩, ⟨687⟩), by decide⟩,
  ⟨(⟨459⟩, ⟨833⟩), by decide⟩]

theorem LP_4_39_inj : Function.Injective LP_4_39 := by decide

theorem LP_4_39_surj : Function.Surjective LP_4_39 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨207⟩, ⟨371⟩, ⟨451⟩, ⟨459⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨207⟩ : QbarCW.Cell) = {⟨807⟩, ⟨830⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨371⟩ : QbarCW.Cell) = {⟨807⟩, ⟨833⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨451⟩ : QbarCW.Cell) = {⟨687⟩, ⟨830⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨459⟩ : QbarCW.Cell) = {⟨687⟩, ⟨833⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_16 : cChain 4 (slabV 4 (tauV4 16)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_18_623_298

theorem chC_4_17 : cChain 4 (slabV 4 (tauV4 17)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_18_635_298

theorem chC_4_18 : cChain 4 (slabV 4 (tauV4 18)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_18_623_350

theorem chC_4_19 : cChain 4 (slabV 4 (tauV4 19)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_18_638_350

theorem chC_4_20 : cChain 4 (slabV 4 (tauV4 20)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_18_629_438

theorem chC_4_21 : cChain 4 (slabV 4 (tauV4 21)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_18_635_438

theorem chC_4_22 : cChain 4 (slabV 4 (tauV4 22)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_18_629_446

theorem chC_4_23 : cChain 4 (slabV 4 (tauV4 23)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446
      = mkSimplex (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_39 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_18_638_446

/-- **Wall leaf (cusp 4, cell 39)**: the 8 wall triangles of cell `39` give its `Ψ_M`-image. -/
theorem wallCell_4_39 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 39), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (39 : Fin 192) • (PsiM.f 2) (Pi.single (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 39) = {16, 17, 18, 19, 20, 21, 22, 23} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_39) LP_4_39_inj LP_4_39_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_16, chC_4_17, chC_4_18, chC_4_19, chC_4_20, chC_4_21, chC_4_22, chC_4_23]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 0).1.1.idx) * qInc (LP_4_39 0).1.1.idx (LP_4_39 0).1.2.idx) = 1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 1).1.1.idx) * qInc (LP_4_39 1).1.1.idx (LP_4_39 1).1.2.idx) = -1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 2).1.1.idx) * qInc (LP_4_39 2).1.1.idx (LP_4_39 2).1.2.idx) = -1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 3).1.1.idx) * qInc (LP_4_39 3).1.1.idx (LP_4_39 3).1.2.idx) = 1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 4).1.1.idx) * qInc (LP_4_39 4).1.1.idx (LP_4_39 4).1.2.idx) = -1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 5).1.1.idx) * qInc (LP_4_39 5).1.1.idx (LP_4_39 5).1.2.idx) = 1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 6).1.1.idx) * qInc (LP_4_39 6).1.1.idx (LP_4_39 6).1.2.idx) = 1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_39 7).1.1.idx) * qInc (LP_4_39 7).1.1.idx (LP_4_39 7).1.2.idx) = -1 := by decide
  have hc : planeCycleVec 4 0 (39 : Fin 192) = -1 := by decide
  have a16 : coefV4 16 = -1 := by decide
  have a17 : coefV4 17 = 1 := by decide
  have a18 : coefV4 18 = 1 := by decide
  have a19 : coefV4 19 = -1 := by decide
  have a20 : coefV4 20 = 1 := by decide
  have a21 : coefV4 21 = -1 := by decide
  have a22 : coefV4 22 = -1 := by decide
  have a23 : coefV4 23 = 1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a16, a17, a18, a19, a20, a21, a22, a23]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 42 (root face 103) -/

/-- The eight `(f,u)`-chains of the root face of cell `42`. -/
def LP_4_42 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨302⟩, ⟨578⟩), by decide⟩,
  ⟨(⟨302⟩, ⟨593⟩), by decide⟩,
  ⟨(⟨398⟩, ⟨578⟩), by decide⟩,
  ⟨(⟨398⟩, ⟨596⟩), by decide⟩,
  ⟨(⟨470⟩, ⟨587⟩), by decide⟩,
  ⟨(⟨470⟩, ⟨593⟩), by decide⟩,
  ⟨(⟨478⟩, ⟨587⟩), by decide⟩,
  ⟨(⟨478⟩, ⟨596⟩), by decide⟩]

theorem LP_4_42_inj : Function.Injective LP_4_42 := by decide

theorem LP_4_42_surj : Function.Surjective LP_4_42 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨302⟩, ⟨398⟩, ⟨470⟩, ⟨478⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨302⟩ : QbarCW.Cell) = {⟨578⟩, ⟨593⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨398⟩ : QbarCW.Cell) = {⟨578⟩, ⟨596⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨470⟩ : QbarCW.Cell) = {⟨587⟩, ⟨593⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨478⟩ : QbarCW.Cell) = {⟨587⟩, ⟨596⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_120 : cChain 4 (slabV 4 (tauV4 120)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_44_840_203

theorem chC_4_121 : cChain 4 (slabV 4 (tauV4 121)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_44_857_203

theorem chC_4_122 : cChain 4 (slabV 4 (tauV4 122)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_44_840_323

theorem chC_4_123 : cChain 4 (slabV 4 (tauV4 123)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_44_860_323

theorem chC_4_124 : cChain 4 (slabV 4 (tauV4 124)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_44_720_419

theorem chC_4_125 : cChain 4 (slabV 4 (tauV4 125)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_44_857_419

theorem chC_4_126 : cChain 4 (slabV 4 (tauV4 126)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_44_720_427

theorem chC_4_127 : cChain 4 (slabV 4 (tauV4 127)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427
      = mkSimplex (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_42 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_44_860_427

/-- **Wall leaf (cusp 4, cell 42)**: the 8 wall triangles of cell `42` give its `Ψ_M`-image. -/
theorem wallCell_4_42 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 42), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (42 : Fin 192) • (PsiM.f 2) (Pi.single (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 42) = {120, 121, 122, 123, 124, 125, 126, 127} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_42) LP_4_42_inj LP_4_42_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_120, chC_4_121, chC_4_122, chC_4_123, chC_4_124, chC_4_125, chC_4_126, chC_4_127]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 0).1.1.idx) * qInc (LP_4_42 0).1.1.idx (LP_4_42 0).1.2.idx) = -1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 1).1.1.idx) * qInc (LP_4_42 1).1.1.idx (LP_4_42 1).1.2.idx) = 1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 2).1.1.idx) * qInc (LP_4_42 2).1.1.idx (LP_4_42 2).1.2.idx) = 1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 3).1.1.idx) * qInc (LP_4_42 3).1.1.idx (LP_4_42 3).1.2.idx) = -1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 4).1.1.idx) * qInc (LP_4_42 4).1.1.idx (LP_4_42 4).1.2.idx) = 1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 5).1.1.idx) * qInc (LP_4_42 5).1.1.idx (LP_4_42 5).1.2.idx) = -1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 6).1.1.idx) * qInc (LP_4_42 6).1.1.idx (LP_4_42 6).1.2.idx) = -1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_42 7).1.1.idx) * qInc (LP_4_42 7).1.1.idx (LP_4_42 7).1.2.idx) = 1 := by decide
  have hc : planeCycleVec 4 0 (42 : Fin 192) = -1 := by decide
  have a120 : coefV4 120 = 1 := by decide
  have a121 : coefV4 121 = -1 := by decide
  have a122 : coefV4 122 = -1 := by decide
  have a123 : coefV4 123 = 1 := by decide
  have a124 : coefV4 124 = -1 := by decide
  have a125 : coefV4 125 = 1 := by decide
  have a126 : coefV4 126 = 1 := by decide
  have a127 : coefV4 127 = -1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a120, a121, a122, a123, a124, a125, a126, a127]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 43 (root face 104) -/

/-- The eight `(f,u)`-chains of the root face of cell `43`. -/
def LP_4_43 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨303⟩, ⟨579⟩), by decide⟩,
  ⟨(⟨303⟩, ⟨614⟩), by decide⟩,
  ⟨(⟨399⟩, ⟨579⟩), by decide⟩,
  ⟨(⟨399⟩, ⟨617⟩), by decide⟩,
  ⟨(⟨466⟩, ⟨608⟩), by decide⟩,
  ⟨(⟨466⟩, ⟨614⟩), by decide⟩,
  ⟨(⟨474⟩, ⟨608⟩), by decide⟩,
  ⟨(⟨474⟩, ⟨617⟩), by decide⟩]

theorem LP_4_43_inj : Function.Injective LP_4_43 := by decide

theorem LP_4_43_surj : Function.Surjective LP_4_43 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨303⟩, ⟨399⟩, ⟨466⟩, ⟨474⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨303⟩ : QbarCW.Cell) = {⟨579⟩, ⟨614⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨399⟩ : QbarCW.Cell) = {⟨579⟩, ⟨617⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨466⟩ : QbarCW.Cell) = {⟨608⟩, ⟨614⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨474⟩ : QbarCW.Cell) = {⟨608⟩, ⟨617⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_88 : cChain 4 (slabV 4 (tauV4 88)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_33_839_202

theorem chC_4_89 : cChain 4 (slabV 4 (tauV4 89)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_33_845_202

theorem chC_4_90 : cChain 4 (slabV 4 (tauV4 90)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_33_839_322

theorem chC_4_91 : cChain 4 (slabV 4 (tauV4 91)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_33_848_322

theorem chC_4_92 : cChain 4 (slabV 4 (tauV4 92)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_33_705_423

theorem chC_4_93 : cChain 4 (slabV 4 (tauV4 93)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_33_845_423

theorem chC_4_94 : cChain 4 (slabV 4 (tauV4 94)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_33_705_431

theorem chC_4_95 : cChain 4 (slabV 4 (tauV4 95)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431
      = mkSimplex (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_43 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_33_848_431

/-- **Wall leaf (cusp 4, cell 43)**: the 8 wall triangles of cell `43` give its `Ψ_M`-image. -/
theorem wallCell_4_43 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 43), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (43 : Fin 192) • (PsiM.f 2) (Pi.single (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 43) = {88, 89, 90, 91, 92, 93, 94, 95} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_43) LP_4_43_inj LP_4_43_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_88, chC_4_89, chC_4_90, chC_4_91, chC_4_92, chC_4_93, chC_4_94, chC_4_95]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 0).1.1.idx) * qInc (LP_4_43 0).1.1.idx (LP_4_43 0).1.2.idx) = -1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 1).1.1.idx) * qInc (LP_4_43 1).1.1.idx (LP_4_43 1).1.2.idx) = 1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 2).1.1.idx) * qInc (LP_4_43 2).1.1.idx (LP_4_43 2).1.2.idx) = 1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 3).1.1.idx) * qInc (LP_4_43 3).1.1.idx (LP_4_43 3).1.2.idx) = -1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 4).1.1.idx) * qInc (LP_4_43 4).1.1.idx (LP_4_43 4).1.2.idx) = 1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 5).1.1.idx) * qInc (LP_4_43 5).1.1.idx (LP_4_43 5).1.2.idx) = -1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 6).1.1.idx) * qInc (LP_4_43 6).1.1.idx (LP_4_43 6).1.2.idx) = -1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_43 7).1.1.idx) * qInc (LP_4_43 7).1.1.idx (LP_4_43 7).1.2.idx) = 1 := by decide
  have hc : planeCycleVec 4 0 (43 : Fin 192) = 1 := by decide
  have a88 : coefV4 88 = -1 := by decide
  have a89 : coefV4 89 = 1 := by decide
  have a90 : coefV4 90 = 1 := by decide
  have a91 : coefV4 91 = -1 := by decide
  have a92 : coefV4 92 = 1 := by decide
  have a93 : coefV4 93 = -1 := by decide
  have a94 : coefV4 94 = -1 := by decide
  have a95 : coefV4 95 = 1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a88, a89, a90, a91, a92, a93, a94, a95]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 44 (root face 105) -/

/-- The eight `(f,u)`-chains of the root face of cell `44`. -/
def LP_4_44 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨270⟩, ⟨734⟩), by decide⟩,
  ⟨(⟨270⟩, ⟨746⟩), by decide⟩,
  ⟨(⟨374⟩, ⟨734⟩), by decide⟩,
  ⟨(⟨374⟩, ⟨749⟩), by decide⟩,
  ⟨(⟨471⟩, ⟨588⟩), by decide⟩,
  ⟨(⟨471⟩, ⟨746⟩), by decide⟩,
  ⟨(⟨479⟩, ⟨588⟩), by decide⟩,
  ⟨(⟨479⟩, ⟨749⟩), by decide⟩]

theorem LP_4_44_inj : Function.Injective LP_4_44 := by decide

theorem LP_4_44_surj : Function.Surjective LP_4_44 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨270⟩, ⟨374⟩, ⟨471⟩, ⟨479⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨270⟩ : QbarCW.Cell) = {⟨734⟩, ⟨746⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨374⟩ : QbarCW.Cell) = {⟨734⟩, ⟨749⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨471⟩ : QbarCW.Cell) = {⟨588⟩, ⟨746⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨479⟩ : QbarCW.Cell) = {⟨588⟩, ⟨749⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_112 : cChain 4 (slabV 4 (tauV4 112)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_40_702_235

theorem chC_4_113 : cChain 4 (slabV 4 (tauV4 113)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_40_725_235

theorem chC_4_114 : cChain 4 (slabV 4 (tauV4 114)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_40_702_347

theorem chC_4_115 : cChain 4 (slabV 4 (tauV4 115)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_40_728_347

theorem chC_4_116 : cChain 4 (slabV 4 (tauV4 116)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_40_719_418

theorem chC_4_117 : cChain 4 (slabV 4 (tauV4 117)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_40_725_418

theorem chC_4_118 : cChain 4 (slabV 4 (tauV4 118)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_40_719_426

theorem chC_4_119 : cChain 4 (slabV 4 (tauV4 119)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426
      = mkSimplex (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_44 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_40_728_426

/-- **Wall leaf (cusp 4, cell 44)**: the 8 wall triangles of cell `44` give its `Ψ_M`-image. -/
theorem wallCell_4_44 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 44), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (44 : Fin 192) • (PsiM.f 2) (Pi.single (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 44) = {112, 113, 114, 115, 116, 117, 118, 119} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_44) LP_4_44_inj LP_4_44_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_112, chC_4_113, chC_4_114, chC_4_115, chC_4_116, chC_4_117, chC_4_118, chC_4_119]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 0).1.1.idx) * qInc (LP_4_44 0).1.1.idx (LP_4_44 0).1.2.idx) = 1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 1).1.1.idx) * qInc (LP_4_44 1).1.1.idx (LP_4_44 1).1.2.idx) = -1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 2).1.1.idx) * qInc (LP_4_44 2).1.1.idx (LP_4_44 2).1.2.idx) = -1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 3).1.1.idx) * qInc (LP_4_44 3).1.1.idx (LP_4_44 3).1.2.idx) = 1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 4).1.1.idx) * qInc (LP_4_44 4).1.1.idx (LP_4_44 4).1.2.idx) = -1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 5).1.1.idx) * qInc (LP_4_44 5).1.1.idx (LP_4_44 5).1.2.idx) = 1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 6).1.1.idx) * qInc (LP_4_44 6).1.1.idx (LP_4_44 6).1.2.idx) = 1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_44 7).1.1.idx) * qInc (LP_4_44 7).1.1.idx (LP_4_44 7).1.2.idx) = -1 := by decide
  have hc : planeCycleVec 4 0 (44 : Fin 192) = -1 := by decide
  have a112 : coefV4 112 = -1 := by decide
  have a113 : coefV4 113 = 1 := by decide
  have a114 : coefV4 114 = 1 := by decide
  have a115 : coefV4 115 = -1 := by decide
  have a116 : coefV4 116 = 1 := by decide
  have a117 : coefV4 117 = -1 := by decide
  have a118 : coefV4 118 = -1 := by decide
  have a119 : coefV4 119 = 1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a112, a113, a114, a115, a116, a117, a118, a119]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 45 (root face 106) -/

/-- The eight `(f,u)`-chains of the root face of cell `45`. -/
def LP_4_45 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨271⟩, ⟨735⟩), by decide⟩,
  ⟨(⟨271⟩, ⟨764⟩), by decide⟩,
  ⟨(⟨375⟩, ⟨735⟩), by decide⟩,
  ⟨(⟨375⟩, ⟨767⟩), by decide⟩,
  ⟨(⟨467⟩, ⟨609⟩), by decide⟩,
  ⟨(⟨467⟩, ⟨764⟩), by decide⟩,
  ⟨(⟨475⟩, ⟨609⟩), by decide⟩,
  ⟨(⟨475⟩, ⟨767⟩), by decide⟩]

theorem LP_4_45_inj : Function.Injective LP_4_45 := by decide

theorem LP_4_45_surj : Function.Surjective LP_4_45 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨271⟩, ⟨375⟩, ⟨467⟩, ⟨475⟩} := by decide
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨271⟩ : QbarCW.Cell) = {⟨735⟩, ⟨764⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨375⟩ : QbarCW.Cell) = {⟨735⟩, ⟨767⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨467⟩ : QbarCW.Cell) = {⟨609⟩, ⟨764⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨475⟩ : QbarCW.Cell) = {⟨609⟩, ⟨767⟩} := by decide
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_64 : cChain 4 (slabV 4 (tauV4 64)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_234
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 0) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_27_701_234

theorem chC_4_65 : cChain 4 (slabV 4 (tauV4 65)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_234
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 1) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_27_710_234

theorem chC_4_66 : cChain 4 (slabV 4 (tauV4 66)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 2) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_27_701_346

theorem chC_4_67 : cChain 4 (slabV 4 (tauV4 67)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 3) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_27_713_346

theorem chC_4_68 : cChain 4 (slabV 4 (tauV4 68)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 4) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_27_704_422

theorem chC_4_69 : cChain 4 (slabV 4 (tauV4 69)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 5) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_27_710_422

theorem chC_4_70 : cChain 4 (slabV 4 (tauV4 70)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 6) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_27_704_430

theorem chC_4_71 : cChain 4 (slabV 4 (tauV4 71)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 7) := by
    ext k; fin_cases k <;> decide
  rw [← hs]
  exact ch_4_27_713_430

/-- **Wall leaf (cusp 4, cell 45)**: the 8 wall triangles of cell `45` give its `Ψ_M`-image. -/
theorem wallCell_4_45 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 45), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (45 : Fin 192) • (PsiM.f 2) (Pi.single (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 45) = {64, 65, 66, 67, 68, 69, 70, 71} := by decide
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_45) LP_4_45_inj LP_4_45_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_64, chC_4_65, chC_4_66, chC_4_67, chC_4_68, chC_4_69, chC_4_70, chC_4_71]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 0).1.1.idx) * qInc (LP_4_45 0).1.1.idx (LP_4_45 0).1.2.idx) = 1 := by decide
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 1).1.1.idx) * qInc (LP_4_45 1).1.1.idx (LP_4_45 1).1.2.idx) = -1 := by decide
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 2).1.1.idx) * qInc (LP_4_45 2).1.1.idx (LP_4_45 2).1.2.idx) = -1 := by decide
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 3).1.1.idx) * qInc (LP_4_45 3).1.1.idx (LP_4_45 3).1.2.idx) = 1 := by decide
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 4).1.1.idx) * qInc (LP_4_45 4).1.1.idx (LP_4_45 4).1.2.idx) = -1 := by decide
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 5).1.1.idx) * qInc (LP_4_45 5).1.1.idx (LP_4_45 5).1.2.idx) = 1 := by decide
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 6).1.1.idx) * qInc (LP_4_45 6).1.1.idx (LP_4_45 6).1.2.idx) = 1 := by decide
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 7).1.1.idx) * qInc (LP_4_45 7).1.1.idx (LP_4_45 7).1.2.idx) = -1 := by decide
  have hc : planeCycleVec 4 0 (45 : Fin 192) = 1 := by decide
  have a64 : coefV4 64 = 1 := by decide
  have a65 : coefV4 65 = -1 := by decide
  have a66 : coefV4 66 = -1 := by decide
  have a67 : coefV4 67 = 1 := by decide
  have a68 : coefV4 68 = -1 := by decide
  have a69 : coefV4 69 = 1 := by decide
  have a70 : coefV4 70 = 1 := by decide
  have a71 : coefV4 71 = -1 := by decide
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a64, a65, a66, a67, a68, a69, a70, a71]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### Assembly for cusp 4 -/

/-- **The wall identification for cusp 4** (untranslated triangles). -/
theorem wallPsi_4 :
    (∑ j : Idx4, coefV4 j • cChain 4 (slabV 4 (tauV4 j))) = (PsiM.f 2) (planeCycleVec 4 0) := by
  have hexp : (planeCycleVec 4 0 : Fin 192 → ℤ)
      = ∑ e ∈ ({24, 25, 26, 27, 30, 31, 32, 33, 36, 37, 38, 39, 42, 43, 44, 45} : Finset (Fin 192)), planeCycleVec 4 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ) := by
    funext i; rw [Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]; revert i; decide
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
    (fun j _ => by revert j; decide)]
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
