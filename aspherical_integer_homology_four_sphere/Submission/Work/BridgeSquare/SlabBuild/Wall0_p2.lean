import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts0
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall0_p1

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



theorem chC_0_20 : cChain 0 (slabV 0 (tauV0 20)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_612_404

theorem chC_0_21 : cChain 0 (slabV 0 (tauV0 21)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_690_404

theorem chC_0_22 : cChain 0 (slabV 0 (tauV0 22)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_591_408

theorem chC_0_23 : cChain 0 (slabV 0 (tauV0 23)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_672_408

/-- **Wall leaf (cusp 0, cell 22)**: the 8 wall triangles of cell `22` give its `Ψ_M`-image. -/
theorem wallCell_0_22 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx0 => cellV0 j = 22), coefV0 j • cChain 0 (slabV 0 (tauV0 j)))
      = planeCycleVec 0 0 (22 : Fin 192) • (PsiM.f 2) (Pi.single (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx0 => cellV0 j = 22) = {16, 17, 18, 19, 20, 21, 22, 23} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_0_22) LP_0_22_inj LP_0_22_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_0_16, chC_0_17, chC_0_18, chC_0_19, chC_0_20, chC_0_21, chC_0_22, chC_0_23]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 0).1.1.idx) * qInc (LP_0_22 0).1.1.idx (LP_0_22 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 1).1.1.idx) * qInc (LP_0_22 1).1.1.idx (LP_0_22 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 2).1.1.idx) * qInc (LP_0_22 2).1.1.idx (LP_0_22 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 3).1.1.idx) * qInc (LP_0_22 3).1.1.idx (LP_0_22 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 4).1.1.idx) * qInc (LP_0_22 4).1.1.idx (LP_0_22 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 5).1.1.idx) * qInc (LP_0_22 5).1.1.idx (LP_0_22 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 6).1.1.idx) * qInc (LP_0_22 6).1.1.idx (LP_0_22 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_22 7).1.1.idx) * qInc (LP_0_22 7).1.1.idx (LP_0_22 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 0 0 (22 : Fin 192) = -1 := by decide +kernel
  have a16 : coefV0 16 = 1 := by decide +kernel
  have a17 : coefV0 17 = -1 := by decide +kernel
  have a18 : coefV0 18 = -1 := by decide +kernel
  have a19 : coefV0 19 = 1 := by decide +kernel
  have a20 : coefV0 20 = -1 := by decide +kernel
  have a21 : coefV0 21 = 1 := by decide +kernel
  have a22 : coefV0 22 = 1 := by decide +kernel
  have a23 : coefV0 23 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a16, a17, a18, a19, a20, a21, a22, a23]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 0, cell 152 (root face 58) -/

/-- The eight `(f,u)`-chains of the root face of cell `152`. -/
def LP_0_152 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨196⟩, ⟨843⟩), by decide +kernel⟩,
  ⟨(⟨196⟩, ⟨855⟩), by decide +kernel⟩,
  ⟨(⟨260⟩, ⟨780⟩), by decide +kernel⟩,
  ⟨(⟨260⟩, ⟨795⟩), by decide +kernel⟩,
  ⟨(⟨332⟩, ⟨795⟩), by decide +kernel⟩,
  ⟨(⟨332⟩, ⟨855⟩), by decide +kernel⟩,
  ⟨(⟨336⟩, ⟨780⟩), by decide +kernel⟩,
  ⟨(⟨336⟩, ⟨843⟩), by decide +kernel⟩]

theorem LP_0_152_inj : Function.Injective LP_0_152 := by decide +kernel

theorem LP_0_152_surj : Function.Surjective LP_0_152 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨196⟩, ⟨260⟩, ⟨332⟩, ⟨336⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨196⟩ : QbarCW.Cell) = {⟨843⟩, ⟨855⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨260⟩ : QbarCW.Cell) = {⟨780⟩, ⟨795⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨332⟩ : QbarCW.Cell) = {⟨795⟩, ⟨855⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨336⟩ : QbarCW.Cell) = {⟨780⟩, ⟨843⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_0_0 : cChain 0 (slabV 0 (tauV0 0)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_196
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_843_196

theorem chC_0_1 : cChain 0 (slabV 0 (tauV0 1)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_196
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_855_196

theorem chC_0_2 : cChain 0 (slabV 0 (tauV0 2)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_260
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_780_260

theorem chC_0_3 : cChain 0 (slabV 0 (tauV0 3)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_260
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_795_260

theorem chC_0_4 : cChain 0 (slabV 0 (tauV0 4)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_332
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_795_332

theorem chC_0_5 : cChain 0 (slabV 0 (tauV0 5)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_332
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_855_332

theorem chC_0_6 : cChain 0 (slabV 0 (tauV0 6)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_336
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_780_336

theorem chC_0_7 : cChain 0 (slabV 0 (tauV0 7)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_336
      = mkSimplex (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_152 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_0_843_336

/-- **Wall leaf (cusp 0, cell 152)**: the 8 wall triangles of cell `152` give its `Ψ_M`-image. -/
theorem wallCell_0_152 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx0 => cellV0 j = 152), coefV0 j • cChain 0 (slabV 0 (tauV0 j)))
      = planeCycleVec 0 0 (152 : Fin 192) • (PsiM.f 2) (Pi.single (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx0 => cellV0 j = 152) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_0_152) LP_0_152_inj LP_0_152_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_0_0, chC_0_1, chC_0_2, chC_0_3, chC_0_4, chC_0_5, chC_0_6, chC_0_7]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 0).1.1.idx) * qInc (LP_0_152 0).1.1.idx (LP_0_152 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 1).1.1.idx) * qInc (LP_0_152 1).1.1.idx (LP_0_152 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 2).1.1.idx) * qInc (LP_0_152 2).1.1.idx (LP_0_152 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 3).1.1.idx) * qInc (LP_0_152 3).1.1.idx (LP_0_152 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 4).1.1.idx) * qInc (LP_0_152 4).1.1.idx (LP_0_152 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 5).1.1.idx) * qInc (LP_0_152 5).1.1.idx (LP_0_152 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 6).1.1.idx) * qInc (LP_0_152 6).1.1.idx (LP_0_152 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨152, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_152 7).1.1.idx) * qInc (LP_0_152 7).1.1.idx (LP_0_152 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 0 0 (152 : Fin 192) = 1 := by decide +kernel
  have a0 : coefV0 0 = -1 := by decide +kernel
  have a1 : coefV0 1 = 1 := by decide +kernel
  have a2 : coefV0 2 = 1 := by decide +kernel
  have a3 : coefV0 3 = -1 := by decide +kernel
  have a4 : coefV0 4 = 1 := by decide +kernel
  have a5 : coefV0 5 = -1 := by decide +kernel
  have a6 : coefV0 6 = -1 := by decide +kernel
  have a7 : coefV0 7 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a0, a1, a2, a3, a4, a5, a6, a7]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 0, cell 158 (root face 65) -/

/-- The eight `(f,u)`-chains of the root face of cell `158`. -/
def LP_0_158 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨228⟩, ⟨708⟩), by decide +kernel⟩,
  ⟨(⟨228⟩, ⟨723⟩), by decide +kernel⟩,
  ⟨(⟨292⟩, ⟨633⟩), by decide +kernel⟩,
  ⟨(⟨292⟩, ⟨651⟩), by decide +kernel⟩,
  ⟨(⟨356⟩, ⟨651⟩), by decide +kernel⟩,
  ⟨(⟨356⟩, ⟨723⟩), by decide +kernel⟩,
  ⟨(⟨360⟩, ⟨633⟩), by decide +kernel⟩,
  ⟨(⟨360⟩, ⟨708⟩), by decide +kernel⟩]


end

end Work.BridgeSquare.SlabBuild
