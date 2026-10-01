import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts1
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall1_p1
import Submission.Work.BridgeSquare.SlabBuild.Wall1_p2

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



theorem LP_1_147_inj : Function.Injective LP_1_147 := by decide +kernel

theorem LP_1_147_surj : Function.Surjective LP_1_147 := by
  rintro ⟨⟨f, u⟩, hf, hu⟩
  have hR : QbarCW.facets (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) = {⟨268⟩, ⟨272⟩, ⟨284⟩, ⟨288⟩} := by decide +kernel
  rw [hR] at hf
  fin_cases hf
  · have hU : QbarCW.facets (⟨268⟩ : QbarCW.Cell) = {⟨783⟩, ⟨798⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · have hU : QbarCW.facets (⟨272⟩ : QbarCW.Cell) = {⟨747⟩, ⟨765⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · have hU : QbarCW.facets (⟨284⟩ : QbarCW.Cell) = {⟨765⟩, ⟨798⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · have hU : QbarCW.facets (⟨288⟩ : QbarCW.Cell) = {⟨747⟩, ⟨783⟩} := by decide +kernel
    rw [hU] at hu
    fin_cases hu
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

theorem chC_1_16 : cChain 1 (slabV 1 (tauV1 16)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 0)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_268
      = mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 0) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_6_783_268

theorem chC_1_17 : cChain 1 (slabV 1 (tauV1 17)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 1)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_268
      = mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 1) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_6_798_268

theorem chC_1_18 : cChain 1 (slabV 1 (tauV1 18)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 2)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_272
      = mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 2) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_6_747_272

theorem chC_1_19 : cChain 1 (slabV 1 (tauV1 19)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 3)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_272
      = mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 3) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_6_765_272

theorem chC_1_20 : cChain 1 (slabV 1 (tauV1 20)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 4)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_284
      = mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 4) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_6_765_284

theorem chC_1_21 : cChain 1 (slabV 1 (tauV1 21)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 5)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_284
      = mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 5) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_6_798_284

theorem chC_1_22 : cChain 1 (slabV 1 (tauV1 22)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 6)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_288
      = mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 6) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_6_747_288

theorem chC_1_23 : cChain 1 (slabV 1 (tauV1 23)) =
    singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 7)))) := by
  have hs : Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_288
      = mkSimplex (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))) (LP_1_147 7) := by
    ext k; fin_cases k <;> decide +kernel
  rw [← hs]
  exact ch_1_6_783_288

/-- **Wall leaf (cusp 1, cell 147)**: the 8 wall triangles of cell `147` give its `Ψ_M`-image. -/
theorem wallCell_1_147 :
    (∑ j ∈ Finset.univ.filter (fun j : Idx1 => cellV1 j = 147), coefV1 j • cChain 1 (slabV 1 (tauV1 j)))
      = planeCycleVec 1 0 (147 : Fin 192) • (PsiM.f 2) (Pi.single (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) (1 : ℤ)) := by
  have hfil : Finset.univ.filter (fun j : Idx1 => cellV1 j = 147) = {16, 17, 18, 19, 20, 21, 22, 23} := by decide +kernel
  rw [hfil, PsiM_rootCx_expand, sum_pairIdx_fin8' _ _ (LP_1_147) LP_1_147_inj LP_1_147_surj, Fin.sum_univ_eight]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [chC_1_16, chC_1_17, chC_1_18, chC_1_19, chC_1_20, chC_1_21, chC_1_22, chC_1_23]
  have k0 : (-(qInc (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_147 0).1.1.idx) * qInc (LP_1_147 0).1.1.idx (LP_1_147 0).1.2.idx) = -1 := by decide +kernel
  have k1 : (-(qInc (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_147 1).1.1.idx) * qInc (LP_1_147 1).1.1.idx (LP_1_147 1).1.2.idx) = 1 := by decide +kernel
  have k2 : (-(qInc (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_147 2).1.1.idx) * qInc (LP_1_147 2).1.1.idx (LP_1_147 2).1.2.idx) = 1 := by decide +kernel
  have k3 : (-(qInc (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_147 3).1.1.idx) * qInc (LP_1_147 3).1.1.idx (LP_1_147 3).1.2.idx) = -1 := by decide +kernel
  have k4 : (-(qInc (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_147 4).1.1.idx) * qInc (LP_1_147 4).1.1.idx (LP_1_147 4).1.2.idx) = 1 := by decide +kernel
  have k5 : (-(qInc (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_147 5).1.1.idx) * qInc (LP_1_147 5).1.1.idx (LP_1_147 5).1.2.idx) = -1 := by decide +kernel
  have k6 : (-(qInc (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_147 6).1.1.idx) * qInc (LP_1_147 6).1.1.idx (LP_1_147 6).1.2.idx) = -1 := by decide +kernel
  have k7 : (-(qInc (Mbar.rootCx 2 (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))).idx (LP_1_147 7).1.1.idx) * qInc (LP_1_147 7).1.1.idx (LP_1_147 7).1.2.idx) = 1 := by decide +kernel
  have hc : planeCycleVec 1 0 (147 : Fin 192) = -1 := by decide +kernel
  have a16 : coefV1 16 = 1 := by decide +kernel
  have a17 : coefV1 17 = -1 := by decide +kernel
  have a18 : coefV1 18 = -1 := by decide +kernel
  have a19 : coefV1 19 = 1 := by decide +kernel
  have a20 : coefV1 20 = -1 := by decide +kernel
  have a21 : coefV1 21 = 1 := by decide +kernel
  have a22 : coefV1 22 = 1 := by decide +kernel
  have a23 : coefV1 23 = -1 := by decide +kernel
  rw [k0, k1, k2, k3, k4, k5, k6, k7, hc, a16, a17, a18, a19, a20, a21, a22, a23]
  simp only [smul_add, one_smul, neg_smul, smul_neg, neg_neg]
  abel

/-! ### Assembly for cusp 1 -/

/-- **The wall identification for cusp 1** (untranslated triangles). -/
theorem wallPsi_1 :
    (∑ j : Idx1, coefV1 j • cChain 1 (slabV 1 (tauV1 j))) = (PsiM.f 2) (planeCycleVec 1 0) := by
  have hexp : (planeCycleVec 1 0 : Fin 192 → ℤ)
      = ∑ e ∈ ({5, 11, 141, 147} : Finset (Fin 192)), planeCycleVec 1 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ) := by
    funext i; rw [Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]; revert i; decide +kernel
  have hR : (PsiM.f 2) (planeCycleVec 1 0)
      = ∑ e ∈ ({5, 11, 141, 147} : Finset (Fin 192)), planeCycleVec 1 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
    calc (PsiM.f 2) (planeCycleVec 1 0)
        = (PsiM.f 2) (∑ e ∈ ({5, 11, 141, 147} : Finset (Fin 192)), planeCycleVec 1 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          congrArg (PsiM.f 2) hexp
      _ = ∑ e ∈ ({5, 11, 141, 147} : Finset (Fin 192)), (PsiM.f 2) (planeCycleVec 1 0 e • (Pi.single e (1 : ℤ) : Fin 192 → ℤ)) :=
          map_sum _ _ _
      _ = ∑ e ∈ ({5, 11, 141, 147} : Finset (Fin 192)), planeCycleVec 1 0 e • (PsiM.f 2) (Pi.single e (1 : ℤ)) :=
          Finset.sum_congr rfl fun e _ => map_zsmul _ _ _
  rw [hR, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := ({5, 11, 141, 147} : Finset (Fin 192))) (g := cellV1)
    (fun j _ => by revert j; decide +kernel)]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact wallCell_1_5
  · exact wallCell_1_11
  · exact wallCell_1_141
  · exact wallCell_1_147

theorem lamV_mem1 (j : Idx1) : slabL 1 (lamV1 j) ∈ Work.Cusp.lattice 1 := by
  have hk1 : Work.Cusp.kv 1 1 ∈ Work.Cusp.lattice 1 := AddSubgroup.subset_closure (Set.mem_range_self 1)
  have hk2 : Work.Cusp.kv 1 2 ∈ Work.Cusp.lattice 1 := AddSubgroup.subset_closure (Set.mem_range_self 2)
  have h : slabL 1 (lamV1 j) ∈ ({0, -Work.Cusp.kv 1 2, -Work.Cusp.kv 1 1, -Work.Cusp.kv 1 1 - Work.Cusp.kv 1 2} : Set CuspE3) := by
    fin_cases j <;> simp [lamV1, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3] <;> abel_nf <;> simp
  rcases h with h | h | h | h <;> rw [h]
  · exact zero_mem _
  · exact neg_mem hk2
  · exact neg_mem hk1
  · exact sub_mem (neg_mem hk1) hk2

/-- **The wall chain of cusp 1 realises `Ψ_M(planeCycleVec 1 0)`** (the `W` of `wall_collar 1`, `s = 1`). -/
theorem wall_slab1 : slabChain 1 2 (wallChain1 : AffC 2) = (PsiM.f 2) (planeCycleVec 1 0) := by
  rw [← wallPsi_1, wallChain1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, slabChain_single_one]
  have h1 : slabV 1 (fun k => tauV1 j k + lamV1 j) = fun k => slabV 1 (tauV1 j) k + slabL 1 (lamV1 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 1 (slabV 1 (tauV1 j)) (slabL 1 (lamV1 j)) (lamV_mem1 j)]

end

end Work.BridgeSquare.SlabBuild
