import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts4
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p1_p2

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



theorem LP_4_30_surj : Function.Surjective LP_4_30 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨298⟩, ⟨350⟩, ⟨438⟩, ⟨446⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨298⟩ : QbarCW.Cell) = {⟨623⟩, ⟨635⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨350⟩ : QbarCW.Cell) = {⟨623⟩, ⟨638⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨438⟩ : QbarCW.Cell) = {⟨629⟩, ⟨635⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨446⟩ : QbarCW.Cell) = {⟨629⟩, ⟨638⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_104 : cChain 4 (slabV 4 (tauV4 104)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_37_807_207

theorem chC_4_105 : cChain 4 (slabV 4 (tauV4 105)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_37_830_207

theorem chC_4_106 : cChain 4 (slabV 4 (tauV4 106)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_37_807_371

theorem chC_4_107 : cChain 4 (slabV 4 (tauV4 107)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_37_833_371

theorem chC_4_108 : cChain 4 (slabV 4 (tauV4 108)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_37_687_451

theorem chC_4_109 : cChain 4 (slabV 4 (tauV4 109)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_37_830_451

theorem chC_4_110 : cChain 4 (slabV 4 (tauV4 110)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_37_687_459

theorem chC_4_111 : cChain 4 (slabV 4 (tauV4 111)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459
      = mkSimplex (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_30 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_37_833_459

/-- **Wall leaf (cusp 4, cell 30)**: the 8 wall triangles of cell `30` give its `Ψ_M`-image. -/
theorem wallCell_4_30 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 30), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (30 : Fin 192) • (PsiM.f 2) (Pi.single (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 30) = {104, 105, 106, 107, 108, 109, 110, 111} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_30) LP_4_30_inj LP_4_30_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_104, chC_4_105, chC_4_106, chC_4_107, chC_4_108, chC_4_109, chC_4_110, chC_4_111]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 0).1.1.idx) * qInc (LP_4_30 0).1.1.idx (LP_4_30 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 1).1.1.idx) * qInc (LP_4_30 1).1.1.idx (LP_4_30 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 2).1.1.idx) * qInc (LP_4_30 2).1.1.idx (LP_4_30 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 3).1.1.idx) * qInc (LP_4_30 3).1.1.idx (LP_4_30 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 4).1.1.idx) * qInc (LP_4_30 4).1.1.idx (LP_4_30 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 5).1.1.idx) * qInc (LP_4_30 5).1.1.idx (LP_4_30 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 6).1.1.idx) * qInc (LP_4_30 6).1.1.idx (LP_4_30 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_30 7).1.1.idx) * qInc (LP_4_30 7).1.1.idx (LP_4_30 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 4 0 (30 : Fin 192) = 1 := by decide +kernel
  have a104 : coefV4 104 = -1 := by decide +kernel
  have a105 : coefV4 105 = 1 := by decide +kernel
  have a106 : coefV4 106 = 1 := by decide +kernel
  have a107 : coefV4 107 = -1 := by decide +kernel
  have a108 : coefV4 108 = 1 := by decide +kernel
  have a109 : coefV4 109 = -1 := by decide +kernel
  have a110 : coefV4 110 = -1 := by decide +kernel
  have a111 : coefV4 111 = 1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a104, a105, a106, a107, a108, a109, a110, a111]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### cusp 4, cell 31 (root face 90) -/

/-- The eight `(f,u)`-chains of the root face of cell `31`. -/
def LP_4_31 : Fin 8 → PairIdx (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) := ![
  ⟨(⟨299⟩, ⟨624⟩), by decide +kernel⟩,
  ⟨(⟨299⟩, ⟨653⟩), by decide +kernel⟩,
  ⟨(⟨351⟩, ⟨624⟩), by decide +kernel⟩,
  ⟨(⟨351⟩, ⟨656⟩), by decide +kernel⟩,
  ⟨(⟨434⟩, ⟨647⟩), by decide +kernel⟩,
  ⟨(⟨434⟩, ⟨653⟩), by decide +kernel⟩,
  ⟨(⟨442⟩, ⟨647⟩), by decide +kernel⟩,
  ⟨(⟨442⟩, ⟨656⟩), by decide +kernel⟩]

theorem LP_4_31_inj : Function.Injective LP_4_31 := by decide +kernel

theorem LP_4_31_surj : Function.Surjective LP_4_31 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨299⟩, ⟨351⟩, ⟨434⟩, ⟨442⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨299⟩ : QbarCW.Cell) = {⟨624⟩, ⟨653⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨351⟩ : QbarCW.Cell) = {⟨624⟩, ⟨656⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨434⟩ : QbarCW.Cell) = {⟨647⟩, ⟨653⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨442⟩ : QbarCW.Cell) = {⟨647⟩, ⟨656⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_48 : cChain 4 (slabV 4 (tauV4 48)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_206
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_24_806_206

theorem chC_4_49 : cChain 4 (slabV 4 (tauV4 49)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_206
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_24_815_206

theorem chC_4_50 : cChain 4 (slabV 4 (tauV4 50)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_370
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_24_806_370

theorem chC_4_51 : cChain 4 (slabV 4 (tauV4 51)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_370
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_24_818_370

theorem chC_4_52 : cChain 4 (slabV 4 (tauV4 52)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_455
      = mkSimplex (Mbar.rootCx 2 (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_31 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_24_669_455


end

end Work.BridgeSquare.SlabBuild
