import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts2
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



/-! ### cusp 2, cell 88 (root face 170) -/

/-- The eight `(f,u)`-chains of the root face of cell `88`. -/
def LP_2_88 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨340⟩, ⟨801⟩), by decide +kernel⟩,
  ⟨(⟨340⟩, ⟨861⟩), by decide +kernel⟩,
  ⟨(⟨364⟩, ⟨657⟩), by decide +kernel⟩,
  ⟨(⟨364⟩, ⟨729⟩), by decide +kernel⟩,
  ⟨(⟨428⟩, ⟨729⟩), by decide +kernel⟩,
  ⟨(⟨428⟩, ⟨861⟩), by decide +kernel⟩,
  ⟨(⟨444⟩, ⟨657⟩), by decide +kernel⟩,
  ⟨(⟨444⟩, ⟨801⟩), by decide +kernel⟩]

theorem LP_2_88_inj : Function.Injective LP_2_88 := by decide +kernel

theorem LP_2_88_surj : Function.Surjective LP_2_88 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨340⟩, ⟨364⟩, ⟨428⟩, ⟨444⟩} := by decide +kernel
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

theorem chC_2_24 : cChain 2 (slabV 2 (tauV2 24)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_344
      = mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_11_786_344

theorem chC_2_25 : cChain 2 (slabV 2 (tauV2 25)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_344
      = mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_11_849_344

theorem chC_2_26 : cChain 2 (slabV 2 (tauV2 26)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_368
      = mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_11_639_368

theorem chC_2_27 : cChain 2 (slabV 2 (tauV2 27)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_368
      = mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_11_714_368

theorem chC_2_28 : cChain 2 (slabV 2 (tauV2 28)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_432
      = mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_11_714_432

theorem chC_2_29 : cChain 2 (slabV 2 (tauV2 29)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_432
      = mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_11_849_432

theorem chC_2_30 : cChain 2 (slabV 2 (tauV2 30)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_448
      = mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_11_639_448

theorem chC_2_31 : cChain 2 (slabV 2 (tauV2 31)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_448
      = mkSimplex (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_88 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_11_786_448

/-- **Wall leaf (cusp 2, cell 88)**: the 8 wall triangles of cell `88` give its `Ψ_M`-image. -/
theorem wallCell_2_88 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx2 => cellV2 j = 88), coefV2 j • cChain 2 (slabV 2 (tauV2 j)))
      = planeCycleVec 2 0 (88 : Fin 192) • (PsiM.f 2) (Pi.single (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx2 => cellV2 j = 88) = {24, 25, 26, 27, 28, 29, 30, 31} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_2_88) LP_2_88_inj LP_2_88_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_2_24, chC_2_25, chC_2_26, chC_2_27, chC_2_28, chC_2_29, chC_2_30, chC_2_31]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_88 0).1.1.idx) * qInc (LP_2_88 0).1.1.idx (LP_2_88 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_88 1).1.1.idx) * qInc (LP_2_88 1).1.1.idx (LP_2_88 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_88 2).1.1.idx) * qInc (LP_2_88 2).1.1.idx (LP_2_88 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_88 3).1.1.idx) * qInc (LP_2_88 3).1.1.idx (LP_2_88 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_88 4).1.1.idx) * qInc (LP_2_88 4).1.1.idx (LP_2_88 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_88 5).1.1.idx) * qInc (LP_2_88 5).1.1.idx (LP_2_88 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_88 6).1.1.idx) * qInc (LP_2_88 6).1.1.idx (LP_2_88 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨88, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_88 7).1.1.idx) * qInc (LP_2_88 7).1.1.idx (LP_2_88 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 2 0 (88 : Fin 192) = 1 := by decide +kernel
  have a24 : coefV2 24 = -1 := by decide +kernel
  have a25 : coefV2 25 = 1 := by decide +kernel
  have a26 : coefV2 26 = 1 := by decide +kernel
  have a27 : coefV2 27 = -1 := by decide +kernel
  have a28 : coefV2 28 = 1 := by decide +kernel
  have a29 : coefV2 29 = -1 := by decide +kernel
  have a30 : coefV2 30 = -1 := by decide +kernel
  have a31 : coefV2 31 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a24, a25, a26, a27, a28, a29, a30, a31]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 2, cell 94 (root face 177) -/

/-- The eight `(f,u)`-chains of the root face of cell `94`. -/
def LP_2_94 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨388⟩, ⟨768⟩), by decide +kernel⟩,
  ⟨(⟨388⟩, ⟨834⟩), by decide +kernel⟩,
  ⟨(⟨412⟩, ⟨618⟩), by decide +kernel⟩,
  ⟨(⟨412⟩, ⟨696⟩), by decide +kernel⟩,
  ⟨(⟨460⟩, ⟨696⟩), by decide +kernel⟩,
  ⟨(⟨460⟩, ⟨834⟩), by decide +kernel⟩,
  ⟨(⟨476⟩, ⟨618⟩), by decide +kernel⟩,
  ⟨(⟨476⟩, ⟨768⟩), by decide +kernel⟩]

theorem LP_2_94_inj : Function.Injective LP_2_94 := by decide +kernel

theorem LP_2_94_surj : Function.Surjective LP_2_94 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨388⟩, ⟨412⟩, ⟨460⟩, ⟨476⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨388⟩ : QbarCW.Cell) = {⟨768⟩, ⟨834⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨412⟩ : QbarCW.Cell) = {⟨618⟩, ⟨696⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨460⟩ : QbarCW.Cell) = {⟨696⟩, ⟨834⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨476⟩ : QbarCW.Cell) = {⟨618⟩, ⟨768⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_2_16 : cChain 2 (slabV 2 (tauV2 16)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392
      = mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_10_750_392

theorem chC_2_17 : cChain 2 (slabV 2 (tauV2 17)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392
      = mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_10_819_392

theorem chC_2_18 : cChain 2 (slabV 2 (tauV2 18)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416
      = mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_10_597_416

theorem chC_2_19 : cChain 2 (slabV 2 (tauV2 19)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416
      = mkSimplex (Mbar.rootCx 2 (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_94 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_10_678_416


end

end Work.BridgeSquare.SlabBuild
