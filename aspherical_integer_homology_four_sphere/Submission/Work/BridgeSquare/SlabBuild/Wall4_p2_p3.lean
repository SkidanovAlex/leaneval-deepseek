import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts4
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p1
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p2_p2

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



theorem chC_4_47 : cChain 4 (slabV 4 (tauV4 47)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_447
      = mkSimplex (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_37 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_22_785_447

/-- **Wall leaf (cusp 4, cell 37)**: the 8 wall triangles of cell `37` give its `Ψ_M`-image. -/
theorem wallCell_4_37 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 37), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (37 : Fin 192) • (PsiM.f 2) (Pi.single (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 37) = {40, 41, 42, 43, 44, 45, 46, 47} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_37) LP_4_37_inj LP_4_37_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_40, chC_4_41, chC_4_42, chC_4_43, chC_4_44, chC_4_45, chC_4_46, chC_4_47]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 0).1.1.idx) * qInc (LP_4_37 0).1.1.idx (LP_4_37 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 1).1.1.idx) * qInc (LP_4_37 1).1.1.idx (LP_4_37 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 2).1.1.idx) * qInc (LP_4_37 2).1.1.idx (LP_4_37 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 3).1.1.idx) * qInc (LP_4_37 3).1.1.idx (LP_4_37 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 4).1.1.idx) * qInc (LP_4_37 4).1.1.idx (LP_4_37 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 5).1.1.idx) * qInc (LP_4_37 5).1.1.idx (LP_4_37 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 6).1.1.idx) * qInc (LP_4_37 6).1.1.idx (LP_4_37 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_37 7).1.1.idx) * qInc (LP_4_37 7).1.1.idx (LP_4_37 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 4 0 (37 : Fin 192) = -1 := by decide +kernel
  have a40 : coefV4 40 = 1 := by decide +kernel
  have a41 : coefV4 41 = -1 := by decide +kernel
  have a42 : coefV4 42 = -1 := by decide +kernel
  have a43 : coefV4 43 = 1 := by decide +kernel
  have a44 : coefV4 44 = -1 := by decide +kernel
  have a45 : coefV4 45 = 1 := by decide +kernel
  have a46 : coefV4 46 = 1 := by decide +kernel
  have a47 : coefV4 47 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a40, a41, a42, a43, a44, a45, a46, a47]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 38 (root face 98) -/

/-- The eight `(f,u)`-chains of the root face of cell `38`. -/
def LP_4_38 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨206⟩, ⟨806⟩), by decide +kernel⟩,
  ⟨(⟨206⟩, ⟨815⟩), by decide +kernel⟩,
  ⟨(⟨370⟩, ⟨806⟩), by decide +kernel⟩,
  ⟨(⟨370⟩, ⟨818⟩), by decide +kernel⟩,
  ⟨(⟨455⟩, ⟨669⟩), by decide +kernel⟩,
  ⟨(⟨455⟩, ⟨815⟩), by decide +kernel⟩,
  ⟨(⟨463⟩, ⟨669⟩), by decide +kernel⟩,
  ⟨(⟨463⟩, ⟨818⟩), by decide +kernel⟩]

theorem LP_4_38_inj : Function.Injective LP_4_38 := by decide +kernel

theorem LP_4_38_surj : Function.Surjective LP_4_38 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨206⟩, ⟨370⟩, ⟨455⟩, ⟨463⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨206⟩ : QbarCW.Cell) = {⟨806⟩, ⟨815⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨370⟩ : QbarCW.Cell) = {⟨806⟩, ⟨818⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨455⟩ : QbarCW.Cell) = {⟨669⟩, ⟨815⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨463⟩ : QbarCW.Cell) = {⟨669⟩, ⟨818⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_72 : cChain 4 (slabV 4 (tauV4 72)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_624_299

theorem chC_4_73 : cChain 4 (slabV 4 (tauV4 73)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_653_299

theorem chC_4_74 : cChain 4 (slabV 4 (tauV4 74)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_624_351

theorem chC_4_75 : cChain 4 (slabV 4 (tauV4 75)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_656_351

theorem chC_4_76 : cChain 4 (slabV 4 (tauV4 76)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_647_434

theorem chC_4_77 : cChain 4 (slabV 4 (tauV4 77)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_653_434

theorem chC_4_78 : cChain 4 (slabV 4 (tauV4 78)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_647_442

theorem chC_4_79 : cChain 4 (slabV 4 (tauV4 79)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442
      = mkSimplex (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_38 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_28_656_442

/-- **Wall leaf (cusp 4, cell 38)**: the 8 wall triangles of cell `38` give its `Ψ_M`-image. -/
theorem wallCell_4_38 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 38), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (38 : Fin 192) • (PsiM.f 2) (Pi.single (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 38) = {72, 73, 74, 75, 76, 77, 78, 79} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_38) LP_4_38_inj LP_4_38_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_72, chC_4_73, chC_4_74, chC_4_75, chC_4_76, chC_4_77, chC_4_78, chC_4_79]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 0).1.1.idx) * qInc (LP_4_38 0).1.1.idx (LP_4_38 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 1).1.1.idx) * qInc (LP_4_38 1).1.1.idx (LP_4_38 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 2).1.1.idx) * qInc (LP_4_38 2).1.1.idx (LP_4_38 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 3).1.1.idx) * qInc (LP_4_38 3).1.1.idx (LP_4_38 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 4).1.1.idx) * qInc (LP_4_38 4).1.1.idx (LP_4_38 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 5).1.1.idx) * qInc (LP_4_38 5).1.1.idx (LP_4_38 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 6).1.1.idx) * qInc (LP_4_38 6).1.1.idx (LP_4_38 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_38 7).1.1.idx) * qInc (LP_4_38 7).1.1.idx (LP_4_38 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (38 : Fin 192) = 1 := by decide +kernel
  have a72 : coefV4 72 = 1 := by decide +kernel
  have a73 : coefV4 73 = -1 := by decide +kernel
  have a74 : coefV4 74 = -1 := by decide +kernel
  have a75 : coefV4 75 = 1 := by decide +kernel
  have a76 : coefV4 76 = -1 := by decide +kernel
  have a77 : coefV4 77 = 1 := by decide +kernel
  have a78 : coefV4 78 = 1 := by decide +kernel
  have a79 : coefV4 79 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a72, a73, a74, a75, a76, a77, a78, a79]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 39 (root face 99) -/

/-- The eight `(f,u)`-chains of the root face of cell `39`. -/
def LP_4_39 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨207⟩, ⟨807⟩), by decide +kernel⟩,
  ⟨(⟨207⟩, ⟨830⟩), by decide +kernel⟩,
  ⟨(⟨371⟩, ⟨807⟩), by decide +kernel⟩,
  ⟨(⟨371⟩, ⟨833⟩), by decide +kernel⟩,
  ⟨(⟨451⟩, ⟨687⟩), by decide +kernel⟩,
  ⟨(⟨451⟩, ⟨830⟩), by decide +kernel⟩,
  ⟨(⟨459⟩, ⟨687⟩), by decide +kernel⟩,
  ⟨(⟨459⟩, ⟨833⟩), by decide +kernel⟩]

theorem LP_4_39_inj : Function.Injective LP_4_39 := by decide +kernel


end

end Work.BridgeSquare.SlabBuild
