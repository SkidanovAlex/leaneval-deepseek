import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts2
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall2_p1
import Submission.Work.BridgeSquare.SlabBuild.Wall2_p2

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



theorem LP_2_182_inj : Function.Injective LP_2_182 := by decide +kernel

theorem LP_2_182_surj : Function.Surjective LP_2_182 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨388⟩, ⟨412⟩, ⟨460⟩, ⟨476⟩} := by decide +kernel
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

theorem chC_2_8 : cChain 2 (slabV 2 (tauV2 8)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388
      = mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_9_768_388

theorem chC_2_9 : cChain 2 (slabV 2 (tauV2 9)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388
      = mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_9_834_388

theorem chC_2_10 : cChain 2 (slabV 2 (tauV2 10)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_412
      = mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_9_618_412

theorem chC_2_11 : cChain 2 (slabV 2 (tauV2 11)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412
      = mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_9_696_412

theorem chC_2_12 : cChain 2 (slabV 2 (tauV2 12)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460
      = mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_9_696_460

theorem chC_2_13 : cChain 2 (slabV 2 (tauV2 13)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460
      = mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_9_834_460

theorem chC_2_14 : cChain 2 (slabV 2 (tauV2 14)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476
      = mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_9_618_476

theorem chC_2_15 : cChain 2 (slabV 2 (tauV2 15)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476
      = mkSimplex (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_2_182 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_2_9_768_476

/-- **Wall leaf (cusp 2, cell 182)**: the 8 wall triangles of cell `182` give its `Ψ_M`-image. -/
theorem wallCell_2_182 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx2 => cellV2 j = 182), coefV2 j • cChain 2 (slabV 2 (tauV2 j)))
      = planeCycleVec 2 0 (182 : Fin 192) • (PsiM.f 2) (Pi.single (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx2 => cellV2 j = 182) = {8, 9, 10, 11, 12, 13, 14, 15} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_2_182) LP_2_182_inj LP_2_182_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_2_8, chC_2_9, chC_2_10, chC_2_11, chC_2_12, chC_2_13, chC_2_14, chC_2_15]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_182 0).1.1.idx) * qInc (LP_2_182 0).1.1.idx (LP_2_182 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_182 1).1.1.idx) * qInc (LP_2_182 1).1.1.idx (LP_2_182 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_182 2).1.1.idx) * qInc (LP_2_182 2).1.1.idx (LP_2_182 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_182 3).1.1.idx) * qInc (LP_2_182 3).1.1.idx (LP_2_182 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_182 4).1.1.idx) * qInc (LP_2_182 4).1.1.idx (LP_2_182 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_182 5).1.1.idx) * qInc (LP_2_182 5).1.1.idx (LP_2_182 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_182 6).1.1.idx) * qInc (LP_2_182 6).1.1.idx (LP_2_182 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_2_182 7).1.1.idx) * qInc (LP_2_182 7).1.1.idx (LP_2_182 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 2 0 (182 : Fin 192) = -1 := by decide +kernel
  have a8 : coefV2 8 = 1 := by decide +kernel
  have a9 : coefV2 9 = -1 := by decide +kernel
  have a10 : coefV2 10 = -1 := by decide +kernel
  have a11 : coefV2 11 = 1 := by decide +kernel
  have a12 : coefV2 12 = -1 := by decide +kernel
  have a13 : coefV2 13 = 1 := by decide +kernel
  have a14 : coefV2 14 = 1 := by decide +kernel
  have a15 : coefV2 15 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a8, a9, a10, a11, a12, a13, a14, a15]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### Assembly for cusp 2 -/

/-- **The wall identification for cusp 2** (untranslated triangles). -/
theorem wallPsi_2 :
    (∑ j : Idx2, coefV2 j • cChain 2 (slabV 2 (tauV2 j))) = (PsiM.f 2) (planeCycleVec 2 0) := by
  have hexp : (planeCycleVec 2 0 : Fin 192 → ℤ)
      = ∑ e ∈ ({88, 94, 176, 182} : Finset (Fin 192)), planeCycleVec 2 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ) := by
    funext i; rw [Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]; revert i; decide +kernel
  have hR : (PsiM.f 2) (planeCycleVec 2 0)
      = ∑ e ∈ ({88, 94, 176, 182} : Finset (Fin 192)), planeCycleVec 2 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
    calc (PsiM.f 2) (planeCycleVec 2 0)
        = (PsiM.f 2) (∑ e ∈ ({88, 94, 176, 182} : Finset (Fin 192)), planeCycleVec 2 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          congrArg (PsiM.f 2) hexp
      _ = ∑ e ∈ ({88, 94, 176, 182} : Finset (Fin 192)), (PsiM.f 2) (planeCycleVec 2 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          map_sum _ _ _
      _ = ∑ e ∈ ({88, 94, 176, 182} : Finset (Fin 192)), planeCycleVec 2 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
          Finset.sum_congr rfl fun e _ => map_zsmul _ _ _
  rw [hR, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := ({88, 94, 176, 182} : Finset (Fin 192))) (g := cellV2)
    (fun j _ => by revert j; decide +kernel)]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact wallCell_2_88
  · exact wallCell_2_94
  · exact wallCell_2_176
  · exact wallCell_2_182

theorem lamV_mem2 (j : Idx2) : slabL 2 (lamV2 j) ∈ Work.Cusp.lattice 2 := by
  have hk1 : Work.Cusp.kv 2 1 ∈ Work.Cusp.lattice 2 := AddSubgroup.subset_closure (Set.mem_range_self 1)
  have hk2 : Work.Cusp.kv 2 2 ∈ Work.Cusp.lattice 2 := AddSubgroup.subset_closure (Set.mem_range_self 2)
  have h : slabL 2 (lamV2 j) ∈ ({0, -Work.Cusp.kv 2 2, -Work.Cusp.kv 2 1, -Work.Cusp.kv 2 1 - Work.Cusp.kv 2 2} : Set CuspE3) := by
    fin_cases j <;> simp [lamV2, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3] <;> abel_nf <;> simp
  rcases h with h | h | h | h <;> rw [h]
  · exact zero_mem _
  · exact neg_mem hk2
  · exact neg_mem hk1
  · exact sub_mem (neg_mem hk1) hk2

/-- **The wall chain of cusp 2 realises `Ψ_M(planeCycleVec 2 0)`** (the `W` of `wall_collar 2`, `s = 1`). -/
theorem wall_slab2 : slabChain 2 2 (wallChain2 : AffC 2) = (PsiM.f 2) (planeCycleVec 2 0) := by
  rw [← wallPsi_2, wallChain2, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, slabChain_single_one]
  have h1 : slabV 2 (fun k => tauV2 j k + lamV2 j) = fun k => slabV 2 (tauV2 j) k + slabL 2 (lamV2 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 2 (slabV 2 (tauV2 j)) (slabL 2 (lamV2 j)) (lamV_mem2 j)]

end

end Work.BridgeSquare.SlabBuild
