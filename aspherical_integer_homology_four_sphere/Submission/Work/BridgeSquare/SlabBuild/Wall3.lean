import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts3
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



/-! ### cusp 3, cell 77 (root face 143) -/

/-- The eight `(f,u)`-chains of the root face of cell `77`. -/
def LP_3_77 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨484⟩, ⟨837⟩), by decide +kernel⟩,
  ⟨(⟨484⟩, ⟨864⟩), by decide +kernel⟩,
  ⟨(⟨500⟩, ⟨699⟩), by decide +kernel⟩,
  ⟨(⟨500⟩, ⟨732⟩), by decide +kernel⟩,
  ⟨(⟨548⟩, ⟨732⟩), by decide +kernel⟩,
  ⟨(⟨548⟩, ⟨864⟩), by decide +kernel⟩,
  ⟨(⟨552⟩, ⟨699⟩), by decide +kernel⟩,
  ⟨(⟨552⟩, ⟨837⟩), by decide +kernel⟩]

theorem LP_3_77_inj : Function.Injective LP_3_77 := by decide +kernel

theorem LP_3_77_surj : Function.Surjective LP_3_77 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨484⟩, ⟨500⟩, ⟨548⟩, ⟨552⟩} := by decide +kernel
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

theorem chC_3_24 : cChain 3 (slabV 3 (tauV3 24)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_488
      = mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_15_771_488

theorem chC_3_25 : cChain 3 (slabV 3 (tauV3 25)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_488
      = mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_15_804_488

theorem chC_3_26 : cChain 3 (slabV 3 (tauV3 26)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504
      = mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_15_621_504

theorem chC_3_27 : cChain 3 (slabV 3 (tauV3 27)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504
      = mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_15_660_504

theorem chC_3_28 : cChain 3 (slabV 3 (tauV3 28)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556
      = mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_15_660_556

theorem chC_3_29 : cChain 3 (slabV 3 (tauV3 29)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556
      = mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_15_804_556

theorem chC_3_30 : cChain 3 (slabV 3 (tauV3 30)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560
      = mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_15_621_560

theorem chC_3_31 : cChain 3 (slabV 3 (tauV3 31)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_560
      = mkSimplex (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_77 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_15_771_560

/-- **Wall leaf (cusp 3, cell 77)**: the 8 wall triangles of cell `77` give its `Ψ_M`-image. -/
theorem wallCell_3_77 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx3 => cellV3 j = 77), coefV3 j • cChain 3 (slabV 3 (tauV3 j)))
      = planeCycleVec 3 0 (77 : Fin 192) • (PsiM.f 2) (Pi.single (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx3 => cellV3 j = 77) = {24, 25, 26, 27, 28, 29, 30, 31} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_3_77) LP_3_77_inj LP_3_77_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_3_24, chC_3_25, chC_3_26, chC_3_27, chC_3_28, chC_3_29, chC_3_30, chC_3_31]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_77 0).1.1.idx) * qInc (LP_3_77 0).1.1.idx (LP_3_77 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_77 1).1.1.idx) * qInc (LP_3_77 1).1.1.idx (LP_3_77 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_77 2).1.1.idx) * qInc (LP_3_77 2).1.1.idx (LP_3_77 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_77 3).1.1.idx) * qInc (LP_3_77 3).1.1.idx (LP_3_77 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_77 4).1.1.idx) * qInc (LP_3_77 4).1.1.idx (LP_3_77 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_77 5).1.1.idx) * qInc (LP_3_77 5).1.1.idx (LP_3_77 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_77 6).1.1.idx) * qInc (LP_3_77 6).1.1.idx (LP_3_77 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_77 7).1.1.idx) * qInc (LP_3_77 7).1.1.idx (LP_3_77 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 3 0 (77 : Fin 192) = 1 := by decide +kernel
  have a24 : coefV3 24 = -1 := by decide +kernel
  have a25 : coefV3 25 = 1 := by decide +kernel
  have a26 : coefV3 26 = 1 := by decide +kernel
  have a27 : coefV3 27 = -1 := by decide +kernel
  have a28 : coefV3 28 = 1 := by decide +kernel
  have a29 : coefV3 29 = -1 := by decide +kernel
  have a30 : coefV3 30 = -1 := by decide +kernel
  have a31 : coefV3 31 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a24, a25, a26, a27, a28, a29, a30, a31]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 3, cell 83 (root face 157) -/

/-- The eight `(f,u)`-chains of the root face of cell `83`. -/
def LP_3_83 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨516⟩, ⟨822⟩), by decide +kernel⟩,
  ⟨(⟨516⟩, ⟨852⟩), by decide +kernel⟩,
  ⟨(⟨532⟩, ⟨681⟩), by decide +kernel⟩,
  ⟨(⟨532⟩, ⟨717⟩), by decide +kernel⟩,
  ⟨(⟨564⟩, ⟨717⟩), by decide +kernel⟩,
  ⟨(⟨564⟩, ⟨852⟩), by decide +kernel⟩,
  ⟨(⟨568⟩, ⟨681⟩), by decide +kernel⟩,
  ⟨(⟨568⟩, ⟨822⟩), by decide +kernel⟩]

theorem LP_3_83_inj : Function.Injective LP_3_83 := by decide +kernel

theorem LP_3_83_surj : Function.Surjective LP_3_83 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨516⟩, ⟨532⟩, ⟨564⟩, ⟨568⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨516⟩ : QbarCW.Cell) = {⟨822⟩, ⟨852⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨532⟩ : QbarCW.Cell) = {⟨681⟩, ⟨717⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨564⟩ : QbarCW.Cell) = {⟨717⟩, ⟨852⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨568⟩ : QbarCW.Cell) = {⟨681⟩, ⟨822⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_3_8 : cChain 3 (slabV 3 (tauV3 8)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_520
      = mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_13_753_520

theorem chC_3_9 : cChain 3 (slabV 3 (tauV3 9)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_520
      = mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_13_789_520

theorem chC_3_10 : cChain 3 (slabV 3 (tauV3 10)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_536
      = mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_13_600_536

theorem chC_3_11 : cChain 3 (slabV 3 (tauV3 11)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_536
      = mkSimplex (Mbar.rootCx 2 (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_83 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_13_642_536

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

theorem LP_3_171_inj : Function.Injective LP_3_171 := by decide +kernel

theorem LP_3_171_surj : Function.Surjective LP_3_171 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨516⟩, ⟨532⟩, ⟨564⟩, ⟨568⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨516⟩ : QbarCW.Cell) = {⟨822⟩, ⟨852⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨532⟩ : QbarCW.Cell) = {⟨681⟩, ⟨717⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨564⟩ : QbarCW.Cell) = {⟨717⟩, ⟨852⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨568⟩ : QbarCW.Cell) = {⟨681⟩, ⟨822⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_3_16 : cChain 3 (slabV 3 (tauV3 16)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516
      = mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_14_822_516

theorem chC_3_17 : cChain 3 (slabV 3 (tauV3 17)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516
      = mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_14_852_516

theorem chC_3_18 : cChain 3 (slabV 3 (tauV3 18)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532
      = mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_14_681_532

theorem chC_3_19 : cChain 3 (slabV 3 (tauV3 19)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532
      = mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_14_717_532

theorem chC_3_20 : cChain 3 (slabV 3 (tauV3 20)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564
      = mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_14_717_564

theorem chC_3_21 : cChain 3 (slabV 3 (tauV3 21)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_564
      = mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_14_852_564

theorem chC_3_22 : cChain 3 (slabV 3 (tauV3 22)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_568
      = mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_14_681_568

theorem chC_3_23 : cChain 3 (slabV 3 (tauV3 23)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_568
      = mkSimplex (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_3_171 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_3_14_822_568

/-- **Wall leaf (cusp 3, cell 171)**: the 8 wall triangles of cell `171` give its `Ψ_M`-image. -/
theorem wallCell_3_171 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx3 => cellV3 j = 171), coefV3 j • cChain 3 (slabV 3 (tauV3 j)))
      = planeCycleVec 3 0 (171 : Fin 192) • (PsiM.f 2) (Pi.single (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx3 => cellV3 j = 171) = {16, 17, 18, 19, 20, 21, 22, 23} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_3_171) LP_3_171_inj LP_3_171_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_3_16, chC_3_17, chC_3_18, chC_3_19, chC_3_20, chC_3_21, chC_3_22, chC_3_23]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_171 0).1.1.idx) * qInc (LP_3_171 0).1.1.idx (LP_3_171 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_171 1).1.1.idx) * qInc (LP_3_171 1).1.1.idx (LP_3_171 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_171 2).1.1.idx) * qInc (LP_3_171 2).1.1.idx (LP_3_171 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_171 3).1.1.idx) * qInc (LP_3_171 3).1.1.idx (LP_3_171 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_171 4).1.1.idx) * qInc (LP_3_171 4).1.1.idx (LP_3_171 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_171 5).1.1.idx) * qInc (LP_3_171 5).1.1.idx (LP_3_171 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_171 6).1.1.idx) * qInc (LP_3_171 6).1.1.idx (LP_3_171 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_3_171 7).1.1.idx) * qInc (LP_3_171 7).1.1.idx (LP_3_171 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 3 0 (171 : Fin 192) = -1 := by decide +kernel
  have a16 : coefV3 16 = 1 := by decide +kernel
  have a17 : coefV3 17 = -1 := by decide +kernel
  have a18 : coefV3 18 = -1 := by decide +kernel
  have a19 : coefV3 19 = 1 := by decide +kernel
  have a20 : coefV3 20 = -1 := by decide +kernel
  have a21 : coefV3 21 = 1 := by decide +kernel
  have a22 : coefV3 22 = 1 := by decide +kernel
  have a23 : coefV3 23 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a16, a17, a18, a19, a20, a21, a22, a23]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### Assembly for cusp 3 -/

/-- **The wall identification for cusp 3** (untranslated triangles). -/
theorem wallPsi_3 :
    (∑ j : Idx3, coefV3 j • cChain 3 (slabV 3 (tauV3 j))) = (PsiM.f 2) (planeCycleVec 3 0) := by
  have hexp : (planeCycleVec 3 0 : Fin 192 → ℤ)
      = ∑ e ∈ ({77, 83, 165, 171} : Finset (Fin 192)), planeCycleVec 3 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ) := by
    funext i; rw [Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]; revert i; decide +kernel
  have hR : (PsiM.f 2) (planeCycleVec 3 0)
      = ∑ e ∈ ({77, 83, 165, 171} : Finset (Fin 192)), planeCycleVec 3 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
    calc (PsiM.f 2) (planeCycleVec 3 0)
        = (PsiM.f 2) (∑ e ∈ ({77, 83, 165, 171} : Finset (Fin 192)), planeCycleVec 3 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          congrArg (PsiM.f 2) hexp
      _ = ∑ e ∈ ({77, 83, 165, 171} : Finset (Fin 192)), (PsiM.f 2) (planeCycleVec 3 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          map_sum _ _ _
      _ = ∑ e ∈ ({77, 83, 165, 171} : Finset (Fin 192)), planeCycleVec 3 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
          Finset.sum_congr rfl fun e _ => map_zsmul _ _ _
  rw [hR, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := ({77, 83, 165, 171} : Finset (Fin 192))) (g := cellV3)
    (fun j _ => by revert j; decide +kernel)]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact wallCell_3_77
  · exact wallCell_3_83
  · exact wallCell_3_165
  · exact wallCell_3_171

theorem lamV_mem3 (j : Idx3) : slabL 3 (lamV3 j) ∈ Work.Cusp.lattice 3 := by
  have hk1 : Work.Cusp.kv 3 1 ∈ Work.Cusp.lattice 3 := AddSubgroup.subset_closure (Set.mem_range_self 1)
  have hk2 : Work.Cusp.kv 3 2 ∈ Work.Cusp.lattice 3 := AddSubgroup.subset_closure (Set.mem_range_self 2)
  have h : slabL 3 (lamV3 j) ∈ ({0, -Work.Cusp.kv 3 2, -Work.Cusp.kv 3 1, -Work.Cusp.kv 3 1 - Work.Cusp.kv 3 2} : Set CuspE3) := by
    fin_cases j <;> simp [lamV3, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3] <;> abel_nf <;> simp
  rcases h with h | h | h | h <;> rw [h]
  · exact zero_mem _
  · exact neg_mem hk2
  · exact neg_mem hk1
  · exact sub_mem (neg_mem hk1) hk2

/-- **The wall chain of cusp 3 realises `Ψ_M(planeCycleVec 3 0)`** (the `W` of `wall_collar 3`, `s = 1`). -/
theorem wall_slab3 : slabChain 3 2 (wallChain3 : AffC 2) = (PsiM.f 2) (planeCycleVec 3 0) := by
  rw [← wallPsi_3, wallChain3, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, slabChain_single_one]
  have h1 : slabV 3 (fun k => tauV3 j k + lamV3 j) = fun k => slabV 3 (tauV3 j) k + slabL 3 (lamV3 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 3 (slabV 3 (tauV3 j)) (slabL 3 (lamV3 j)) (lamV_mem3 j)]

end

end Work.BridgeSquare.SlabBuild
