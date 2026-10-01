import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Charts3
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Wall3_p1
import Submission.Work.BridgeSquare.SlabBuild.Wall3_p2

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
