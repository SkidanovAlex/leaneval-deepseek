import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts4_p1
import Submission.Work.BridgeSquare.SlabBuild.Charts4_p2

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

noncomputable section

/-- The chart identity of the flag `(839,202,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_839_202 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_839_202 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (839 : Fin 865)
      exact leaf_4_33_839
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (202 : Fin 865)
      exact leaf_4_33_202
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_839_202 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_839_202) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_839_202)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_839_202
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨839⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨839⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide +kernel) (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(845,202,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_845_202 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_845_202 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (845 : Fin 865)
      exact leaf_4_33_845
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (202 : Fin 865)
      exact leaf_4_33_202
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_845_202 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_845_202) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_845_202)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_845_202
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨845⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨845⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide +kernel) (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(839,322,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_839_322 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_839_322 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (839 : Fin 865)
      exact leaf_4_33_839
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (322 : Fin 865)
      exact leaf_4_33_322
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_839_322 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_839_322) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_839_322)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_839_322
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨839⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨839⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide +kernel) (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(848,322,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_848_322 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_848_322 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (848 : Fin 865)
      exact leaf_4_33_848
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (322 : Fin 865)
      exact leaf_4_33_322
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_848_322 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_848_322) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_848_322)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_848_322
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨848⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨848⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide +kernel) (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(705,423,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_705_423 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_705_423 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (705 : Fin 865)
      exact leaf_4_33_705
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (423 : Fin 865)
      exact leaf_4_33_423
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_705_423 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_705_423) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_705_423)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_705_423
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨705⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨705⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide +kernel) (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(845,423,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_845_423 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_845_423 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (845 : Fin 865)
      exact leaf_4_33_845
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (423 : Fin 865)
      exact leaf_4_33_423
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_845_423 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_845_423) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_845_423)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_845_423
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨845⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨845⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide +kernel) (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(705,431,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_705_431 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_705_431 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (705 : Fin 865)
      exact leaf_4_33_705
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (431 : Fin 865)
      exact leaf_4_33_431
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_705_431 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_705_431) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_705_431)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_705_431
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨705⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨705⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide +kernel) (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(848,431,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_848_431 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_848_431 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (848 : Fin 865)
      exact leaf_4_33_848
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (431 : Fin 865)
      exact leaf_4_33_431
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_848_431 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_848_431) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_848_431)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_848_431
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨848⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨848⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide +kernel) (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(774,267,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_774_267 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_774_267 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (774 : Fin 865)
      exact leaf_4_34_774
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (267 : Fin 865)
      exact leaf_4_34_267
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_774_267 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_774_267) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_774_267)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_774_267
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨774⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨774⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide +kernel) (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(797,267,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_797_267 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_797_267 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (797 : Fin 865)
      exact leaf_4_34_797
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (267 : Fin 865)
      exact leaf_4_34_267
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_797_267 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_797_267) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_797_267)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_797_267
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨797⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨797⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide +kernel) (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(774,327,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_774_327 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_774_327 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (774 : Fin 865)
      exact leaf_4_34_774
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (327 : Fin 865)
      exact leaf_4_34_327
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_774_327 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_774_327) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_774_327)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_774_327
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨774⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨774⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide +kernel) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(800,327,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_800_327 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_800_327 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (800 : Fin 865)
      exact leaf_4_34_800
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (327 : Fin 865)
      exact leaf_4_34_327
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_800_327 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_800_327) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_800_327)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_800_327
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨800⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨800⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide +kernel) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(648,435,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_648_435 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_648_435 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (648 : Fin 865)
      exact leaf_4_34_648
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (435 : Fin 865)
      exact leaf_4_34_435
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_648_435 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_648_435) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_648_435)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_648_435
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide +kernel) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(797,435,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_797_435 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_797_435 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (797 : Fin 865)
      exact leaf_4_34_797
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (435 : Fin 865)
      exact leaf_4_34_435
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_797_435 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_797_435) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_797_435)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_797_435
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨797⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨797⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide +kernel) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(648,443,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_648_443 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_648_443 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (648 : Fin 865)
      exact leaf_4_34_648
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (443 : Fin 865)
      exact leaf_4_34_443
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_648_443 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_648_443) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_648_443)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_648_443
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide +kernel) (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(800,443,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_800_443 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_800_443 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (800 : Fin 865)
      exact leaf_4_34_800
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (443 : Fin 865)
      exact leaf_4_34_443
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_800_443 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_800_443) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_800_443)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_800_443
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨800⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨800⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide +kernel) (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(807,207,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_807_207 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_807_207 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (807 : Fin 865)
      exact leaf_4_37_807
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (207 : Fin 865)
      exact leaf_4_37_207
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_807_207 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_807_207) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_807_207)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_807_207
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨807⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨807⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide +kernel) (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(830,207,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_830_207 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_830_207 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (830 : Fin 865)
      exact leaf_4_37_830
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (207 : Fin 865)
      exact leaf_4_37_207
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_830_207 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_830_207) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_830_207)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_830_207
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨830⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨830⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide +kernel) (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(807,371,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_807_371 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_807_371 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (807 : Fin 865)
      exact leaf_4_37_807
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (371 : Fin 865)
      exact leaf_4_37_371
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_807_371 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_807_371) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_807_371)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_807_371
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨807⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨807⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide +kernel) (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(833,371,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_833_371 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_833_371 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (833 : Fin 865)
      exact leaf_4_37_833
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (371 : Fin 865)
      exact leaf_4_37_371
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_833_371 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_833_371) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_833_371)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_833_371
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨833⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨833⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide +kernel) (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(687,451,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_687_451 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_687_451 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (687 : Fin 865)
      exact leaf_4_37_687
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (451 : Fin 865)
      exact leaf_4_37_451
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_687_451 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_687_451) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_687_451)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_687_451
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨687⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨687⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide +kernel) (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(830,451,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_830_451 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_830_451 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (830 : Fin 865)
      exact leaf_4_37_830
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (451 : Fin 865)
      exact leaf_4_37_451
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_830_451 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_830_451) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_830_451)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_830_451
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨830⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨830⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide +kernel) (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
