import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts0
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



/-! ### cusp 0, cell 16 (root face 58) -/

/-- The eight `(f,u)`-chains of the root face of cell `16`. -/
def LP_0_16 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨196⟩, ⟨843⟩), by decide +kernel⟩,
  ⟨(⟨196⟩, ⟨855⟩), by decide +kernel⟩,
  ⟨(⟨260⟩, ⟨780⟩), by decide +kernel⟩,
  ⟨(⟨260⟩, ⟨795⟩), by decide +kernel⟩,
  ⟨(⟨332⟩, ⟨795⟩), by decide +kernel⟩,
  ⟨(⟨332⟩, ⟨855⟩), by decide +kernel⟩,
  ⟨(⟨336⟩, ⟨780⟩), by decide +kernel⟩,
  ⟨(⟨336⟩, ⟨843⟩), by decide +kernel⟩]

theorem LP_0_16_inj : Function.Injective LP_0_16 := by decide +kernel

theorem LP_0_16_surj : Function.Surjective LP_0_16 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨196⟩, ⟨260⟩, ⟨332⟩, ⟨336⟩} := by decide +kernel
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

theorem chC_0_24 : cChain 0 (slabV 0 (tauV0 24)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_813_200

theorem chC_0_25 : cChain 0 (slabV 0 (tauV0 25)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_828_200

theorem chC_0_26 : cChain 0 (slabV 0 (tauV0 26)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_744_264

theorem chC_0_27 : cChain 0 (slabV 0 (tauV0 27)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_762_264

theorem chC_0_28 : cChain 0 (slabV 0 (tauV0 28)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_762_380

theorem chC_0_29 : cChain 0 (slabV 0 (tauV0 29)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_828_380

theorem chC_0_30 : cChain 0 (slabV 0 (tauV0 30)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_744_384

theorem chC_0_31 : cChain 0 (slabV 0 (tauV0 31)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384
      = mkSimplex (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_16 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_3_813_384

/-- **Wall leaf (cusp 0, cell 16)**: the 8 wall triangles of cell `16` give its `Ψ_M`-image. -/
theorem wallCell_0_16 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx0 => cellV0 j = 16), coefV0 j • cChain 0 (slabV 0 (tauV0 j)))
      = planeCycleVec 0 0 (16 : Fin 192) • (PsiM.f 2) (Pi.single (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx0 => cellV0 j = 16) = {24, 25, 26, 27, 28, 29, 30, 31} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_0_16) LP_0_16_inj LP_0_16_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_0_24, chC_0_25, chC_0_26, chC_0_27, chC_0_28, chC_0_29, chC_0_30, chC_0_31]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 0).1.1.idx) * qInc (LP_0_16 0).1.1.idx (LP_0_16 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 1).1.1.idx) * qInc (LP_0_16 1).1.1.idx (LP_0_16 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 2).1.1.idx) * qInc (LP_0_16 2).1.1.idx (LP_0_16 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 3).1.1.idx) * qInc (LP_0_16 3).1.1.idx (LP_0_16 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 4).1.1.idx) * qInc (LP_0_16 4).1.1.idx (LP_0_16 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 5).1.1.idx) * qInc (LP_0_16 5).1.1.idx (LP_0_16 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 6).1.1.idx) * qInc (LP_0_16 6).1.1.idx (LP_0_16 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_0_16 7).1.1.idx) * qInc (LP_0_16 7).1.1.idx (LP_0_16 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 0 0 (16 : Fin 192) = 1 := by decide +kernel
  have a24 : coefV0 24 = -1 := by decide +kernel
  have a25 : coefV0 25 = 1 := by decide +kernel
  have a26 : coefV0 26 = 1 := by decide +kernel
  have a27 : coefV0 27 = -1 := by decide +kernel
  have a28 : coefV0 28 = 1 := by decide +kernel
  have a29 : coefV0 29 = -1 := by decide +kernel
  have a30 : coefV0 30 = -1 := by decide +kernel
  have a31 : coefV0 31 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a24, a25, a26, a27, a28, a29, a30, a31]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 0, cell 22 (root face 65) -/

/-- The eight `(f,u)`-chains of the root face of cell `22`. -/
def LP_0_22 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨228⟩, ⟨708⟩), by decide +kernel⟩,
  ⟨(⟨228⟩, ⟨723⟩), by decide +kernel⟩,
  ⟨(⟨292⟩, ⟨633⟩), by decide +kernel⟩,
  ⟨(⟨292⟩, ⟨651⟩), by decide +kernel⟩,
  ⟨(⟨356⟩, ⟨651⟩), by decide +kernel⟩,
  ⟨(⟨356⟩, ⟨723⟩), by decide +kernel⟩,
  ⟨(⟨360⟩, ⟨633⟩), by decide +kernel⟩,
  ⟨(⟨360⟩, ⟨708⟩), by decide +kernel⟩]

theorem LP_0_22_inj : Function.Injective LP_0_22 := by decide +kernel

theorem LP_0_22_surj : Function.Surjective LP_0_22 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨228⟩, ⟨292⟩, ⟨356⟩, ⟨360⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨228⟩ : QbarCW.Cell) = {⟨708⟩, ⟨723⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨292⟩ : QbarCW.Cell) = {⟨633⟩, ⟨651⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨356⟩ : QbarCW.Cell) = {⟨651⟩, ⟨723⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨360⟩ : QbarCW.Cell) = {⟨633⟩, ⟨708⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_0_16 : cChain 0 (slabV 0 (tauV0 16)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_672_232

theorem chC_0_17 : cChain 0 (slabV 0 (tauV0 17)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_690_232

theorem chC_0_18 : cChain 0 (slabV 0 (tauV0 18)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_591_296

theorem chC_0_19 : cChain 0 (slabV 0 (tauV0 19)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296
      = mkSimplex (Mbar.rootCx 2 (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_0_22 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_0_2_612_296


end

end Work.BridgeSquare.SlabBuild
