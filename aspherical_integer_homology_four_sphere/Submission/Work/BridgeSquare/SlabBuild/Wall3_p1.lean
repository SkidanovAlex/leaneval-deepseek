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


end

end Work.BridgeSquare.SlabBuild
