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
def LP_4_24 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨234⟩, ⟨701⟩), by decide +kernel⟩,
  ⟨(⟨234⟩, ⟨710⟩), by decide +kernel⟩,
  ⟨(⟨346⟩, ⟨701⟩), by decide +kernel⟩,
  ⟨(⟨346⟩, ⟨713⟩), by decide +kernel⟩,
  ⟨(⟨422⟩, ⟨704⟩), by decide +kernel⟩,
  ⟨(⟨422⟩, ⟨710⟩), by decide +kernel⟩,
  ⟨(⟨430⟩, ⟨704⟩), by decide +kernel⟩,
  ⟨(⟨430⟩, ⟨713⟩), by decide +kernel⟩]

theorem LP_4_24_inj : Function.Injective LP_4_24 := by decide +kernel

theorem LP_4_24_surj : Function.Surjective LP_4_24 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨234⟩, ⟨346⟩, ⟨422⟩, ⟨430⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨234⟩ : QbarCW.Cell) = {⟨701⟩, ⟨710⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨346⟩ : QbarCW.Cell) = {⟨701⟩, ⟨713⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨422⟩ : QbarCW.Cell) = {⟨704⟩, ⟨710⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨430⟩ : QbarCW.Cell) = {⟨704⟩, ⟨713⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_56 : cChain 4 (slabV 4 (tauV4 56)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_25_735_271

theorem chC_4_57 : cChain 4 (slabV 4 (tauV4 57)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_25_764_271

theorem chC_4_58 : cChain 4 (slabV 4 (tauV4 58)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_25_735_375

theorem chC_4_59 : cChain 4 (slabV 4 (tauV4 59)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_375
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_25_767_375

theorem chC_4_60 : cChain 4 (slabV 4 (tauV4 60)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_467
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_25_609_467

theorem chC_4_61 : cChain 4 (slabV 4 (tauV4 61)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_467
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_25_764_467

theorem chC_4_62 : cChain 4 (slabV 4 (tauV4 62)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_475
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_25_609_475

theorem chC_4_63 : cChain 4 (slabV 4 (tauV4 63)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_475
      = mkSimplex (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_24 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_25_767_475

/-- **Wall leaf (cusp 4, cell 24)**: the 8 wall triangles of cell `24` give its `Ψ_M`-image. -/
theorem wallCell_4_24 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 24), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (24 : Fin 192) • (PsiM.f 2) (Pi.single (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 24) = {56, 57, 58, 59, 60, 61, 62, 63} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_24) LP_4_24_inj LP_4_24_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_56, chC_4_57, chC_4_58, chC_4_59, chC_4_60, chC_4_61, chC_4_62, chC_4_63]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 0).1.1.idx) * qInc (LP_4_24 0).1.1.idx (LP_4_24 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 1).1.1.idx) * qInc (LP_4_24 1).1.1.idx (LP_4_24 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 2).1.1.idx) * qInc (LP_4_24 2).1.1.idx (LP_4_24 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 3).1.1.idx) * qInc (LP_4_24 3).1.1.idx (LP_4_24 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 4).1.1.idx) * qInc (LP_4_24 4).1.1.idx (LP_4_24 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 5).1.1.idx) * qInc (LP_4_24 5).1.1.idx (LP_4_24 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 6).1.1.idx) * qInc (LP_4_24 6).1.1.idx (LP_4_24 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_24 7).1.1.idx) * qInc (LP_4_24 7).1.1.idx (LP_4_24 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 4 0 (24 : Fin 192) = -1 := by decide +kernel
  have a56 : coefV4 56 = 1 := by decide +kernel
  have a57 : coefV4 57 = -1 := by decide +kernel
  have a58 : coefV4 58 = -1 := by decide +kernel
  have a59 : coefV4 59 = 1 := by decide +kernel
  have a60 : coefV4 60 = -1 := by decide +kernel
  have a61 : coefV4 61 = 1 := by decide +kernel
  have a62 : coefV4 62 = 1 := by decide +kernel
  have a63 : coefV4 63 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a56, a57, a58, a59, a60, a61, a62, a63]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 25 (root face 83) -/

/-- The eight `(f,u)`-chains of the root face of cell `25`. -/
def LP_4_25 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨235⟩, ⟨702⟩), by decide +kernel⟩,
  ⟨(⟨235⟩, ⟨725⟩), by decide +kernel⟩,
  ⟨(⟨347⟩, ⟨702⟩), by decide +kernel⟩,
  ⟨(⟨347⟩, ⟨728⟩), by decide +kernel⟩,
  ⟨(⟨418⟩, ⟨719⟩), by decide +kernel⟩,
  ⟨(⟨418⟩, ⟨725⟩), by decide +kernel⟩,
  ⟨(⟨426⟩, ⟨719⟩), by decide +kernel⟩,
  ⟨(⟨426⟩, ⟨728⟩), by decide +kernel⟩]

theorem LP_4_25_inj : Function.Injective LP_4_25 := by decide +kernel

theorem LP_4_25_surj : Function.Surjective LP_4_25 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨235⟩, ⟨347⟩, ⟨418⟩, ⟨426⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨235⟩ : QbarCW.Cell) = {⟨702⟩, ⟨725⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨347⟩ : QbarCW.Cell) = {⟨702⟩, ⟨728⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨418⟩ : QbarCW.Cell) = {⟨719⟩, ⟨725⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨426⟩ : QbarCW.Cell) = {⟨719⟩, ⟨728⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_8 : cChain 4 (slabV 4 (tauV4 8)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_17_734_270

theorem chC_4_9 : cChain 4 (slabV 4 (tauV4 9)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_17_746_270

theorem chC_4_10 : cChain 4 (slabV 4 (tauV4 10)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_17_734_374

theorem chC_4_11 : cChain 4 (slabV 4 (tauV4 11)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_17_749_374

theorem chC_4_12 : cChain 4 (slabV 4 (tauV4 12)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_17_588_471

theorem chC_4_13 : cChain 4 (slabV 4 (tauV4 13)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_17_746_471

theorem chC_4_14 : cChain 4 (slabV 4 (tauV4 14)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_17_588_479

theorem chC_4_15 : cChain 4 (slabV 4 (tauV4 15)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479
      = mkSimplex (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_25 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_17_749_479

/-- **Wall leaf (cusp 4, cell 25)**: the 8 wall triangles of cell `25` give its `Ψ_M`-image. -/
theorem wallCell_4_25 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 25), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (25 : Fin 192) • (PsiM.f 2) (Pi.single (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 25) = {8, 9, 10, 11, 12, 13, 14, 15} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_25) LP_4_25_inj LP_4_25_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_8, chC_4_9, chC_4_10, chC_4_11, chC_4_12, chC_4_13, chC_4_14, chC_4_15]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 0).1.1.idx) * qInc (LP_4_25 0).1.1.idx (LP_4_25 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 1).1.1.idx) * qInc (LP_4_25 1).1.1.idx (LP_4_25 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 2).1.1.idx) * qInc (LP_4_25 2).1.1.idx (LP_4_25 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 3).1.1.idx) * qInc (LP_4_25 3).1.1.idx (LP_4_25 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 4).1.1.idx) * qInc (LP_4_25 4).1.1.idx (LP_4_25 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 5).1.1.idx) * qInc (LP_4_25 5).1.1.idx (LP_4_25 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 6).1.1.idx) * qInc (LP_4_25 6).1.1.idx (LP_4_25 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_25 7).1.1.idx) * qInc (LP_4_25 7).1.1.idx (LP_4_25 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 4 0 (25 : Fin 192) = 1 := by decide +kernel
  have a8 : coefV4 8 = -1 := by decide +kernel
  have a9 : coefV4 9 = 1 := by decide +kernel
  have a10 : coefV4 10 = 1 := by decide +kernel
  have a11 : coefV4 11 = -1 := by decide +kernel
  have a12 : coefV4 12 = 1 := by decide +kernel
  have a13 : coefV4 13 = -1 := by decide +kernel
  have a14 : coefV4 14 = -1 := by decide +kernel
  have a15 : coefV4 15 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a8, a9, a10, a11, a12, a13, a14, a15]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 26 (root face 84) -/

/-- The eight `(f,u)`-chains of the root face of cell `26`. -/
def LP_4_26 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨202⟩, ⟨839⟩), by decide +kernel⟩,
  ⟨(⟨202⟩, ⟨845⟩), by decide +kernel⟩,
  ⟨(⟨322⟩, ⟨839⟩), by decide +kernel⟩,
  ⟨(⟨322⟩, ⟨848⟩), by decide +kernel⟩,
  ⟨(⟨423⟩, ⟨705⟩), by decide +kernel⟩,
  ⟨(⟨423⟩, ⟨845⟩), by decide +kernel⟩,
  ⟨(⟨431⟩, ⟨705⟩), by decide +kernel⟩,
  ⟨(⟨431⟩, ⟨848⟩), by decide +kernel⟩]

theorem LP_4_26_inj : Function.Injective LP_4_26 := by decide +kernel



end

end Work.BridgeSquare.SlabBuild
