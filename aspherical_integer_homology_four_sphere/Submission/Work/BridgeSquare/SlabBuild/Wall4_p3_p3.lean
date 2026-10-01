import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts4
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p1
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p2
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p3_p1
import Submission.Work.BridgeSquare.SlabBuild.Wall4_p3_p2

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



theorem LP_4_45_surj : Function.Surjective LP_4_45 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨271⟩, ⟨375⟩, ⟨467⟩, ⟨475⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨271⟩ : QbarCW.Cell) = {⟨735⟩, ⟨764⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨375⟩ : QbarCW.Cell) = {⟨735⟩, ⟨767⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨467⟩ : QbarCW.Cell) = {⟨609⟩, ⟨764⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨475⟩ : QbarCW.Cell) = {⟨609⟩, ⟨767⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_4_64 : cChain 4 (slabV 4 (tauV4 64)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_234
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_701_234

theorem chC_4_65 : cChain 4 (slabV 4 (tauV4 65)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_234
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_710_234

theorem chC_4_66 : cChain 4 (slabV 4 (tauV4 66)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_701_346

theorem chC_4_67 : cChain 4 (slabV 4 (tauV4 67)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_713_346

theorem chC_4_68 : cChain 4 (slabV 4 (tauV4 68)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_704_422

theorem chC_4_69 : cChain 4 (slabV 4 (tauV4 69)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_710_422

theorem chC_4_70 : cChain 4 (slabV 4 (tauV4 70)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_704_430

theorem chC_4_71 : cChain 4 (slabV 4 (tauV4 71)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430
      = mkSimplex (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_4_45 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_4_27_713_430

/-- **Wall leaf (cusp 4, cell 45)**: the 8 wall triangles of cell `45` give its `Ψ_M`-image. -/
theorem wallCell_4_45 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx4 => cellV4 j = 45), coefV4 j • cChain 4 (slabV 4 (tauV4 j)))
      = planeCycleVec 4 0 (45 : Fin 192) • (PsiM.f 2) (Pi.single (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx4 => cellV4 j = 45) = {64, 65, 66, 67, 68, 69, 70, 71} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_4_45) LP_4_45_inj LP_4_45_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_4_64, chC_4_65, chC_4_66, chC_4_67, chC_4_68, chC_4_69, chC_4_70, chC_4_71]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 0).1.1.idx) * qInc (LP_4_45 0).1.1.idx (LP_4_45 0).1.2.idx) = 1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 1).1.1.idx) * qInc (LP_4_45 1).1.1.idx (LP_4_45 1).1.2.idx) = -1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 2).1.1.idx) * qInc (LP_4_45 2).1.1.idx (LP_4_45 2).1.2.idx) = -1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 3).1.1.idx) * qInc (LP_4_45 3).1.1.idx (LP_4_45 3).1.2.idx) = 1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 4).1.1.idx) * qInc (LP_4_45 4).1.1.idx (LP_4_45 4).1.2.idx) = -1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 5).1.1.idx) * qInc (LP_4_45 5).1.1.idx (LP_4_45 5).1.2.idx) = 1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 6).1.1.idx) * qInc (LP_4_45 6).1.1.idx (LP_4_45 6).1.2.idx) = 1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_4_45 7).1.1.idx) * qInc (LP_4_45 7).1.1.idx (LP_4_45 7).1.2.idx) = -1 := by decide +kernel
  have hc : planeCycleVec 4 0 (45 : Fin 192) = 1 := by decide +kernel
  have a64 : coefV4 64 = 1 := by decide +kernel
  have a65 : coefV4 65 = -1 := by decide +kernel
  have a66 : coefV4 66 = -1 := by decide +kernel
  have a67 : coefV4 67 = 1 := by decide +kernel
  have a68 : coefV4 68 = -1 := by decide +kernel
  have a69 : coefV4 69 = 1 := by decide +kernel
  have a70 : coefV4 70 = 1 := by decide +kernel
  have a71 : coefV4 71 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a64, a65, a66, a67, a68, a69, a70, a71]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### Assembly for cusp 4 -/

/-- **The wall identification for cusp 4** (untranslated triangles). -/
theorem wallPsi_4 :
    (∑ j : Idx4, coefV4 j • cChain 4 (slabV 4 (tauV4 j))) = (PsiM.f 2) (planeCycleVec 4 0) := by
  have hexp : (planeCycleVec 4 0 : Fin 192 → ℤ)
      = ∑ e ∈ ({24, 25, 26, 27, 30, 31, 32, 33, 36, 37, 38, 39, 42, 43, 44, 45} : Finset (Fin 192)), planeCycleVec 4 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ) := by
    funext i; rw [Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]; revert i; decide +kernel
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
    (fun j _ => by revert j; decide +kernel)]
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
