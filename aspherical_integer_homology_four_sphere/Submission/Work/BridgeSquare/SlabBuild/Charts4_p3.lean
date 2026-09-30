import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts4_p1

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

/-- The chart identity of the flag `(578,302,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_578_302 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_578_302 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (578 : Fin 865)
      exact leaf_4_16_578
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (302 : Fin 865)
      exact leaf_4_16_302
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] fl_4_16_578_302 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_578_302) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_578_302)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_578_302
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨578⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨578⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide +kernel) (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(593,302,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_593_302 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_593_302 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (593 : Fin 865)
      exact leaf_4_16_593
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (302 : Fin 865)
      exact leaf_4_16_302
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] fl_4_16_593_302 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_593_302) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_593_302)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_593_302
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨593⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨593⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide +kernel) (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(578,398,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_578_398 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_578_398 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (578 : Fin 865)
      exact leaf_4_16_578
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (398 : Fin 865)
      exact leaf_4_16_398
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] fl_4_16_578_398 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_578_398) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_578_398)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_578_398
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨578⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨578⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide +kernel) (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(596,398,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_596_398 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_596_398 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (596 : Fin 865)
      exact leaf_4_16_596
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (398 : Fin 865)
      exact leaf_4_16_398
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] fl_4_16_596_398 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_596_398) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_596_398)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_596_398
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨596⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨596⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide +kernel) (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(587,470,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_587_470 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_587_470 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (587 : Fin 865)
      exact leaf_4_16_587
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (470 : Fin 865)
      exact leaf_4_16_470
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] fl_4_16_587_470 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_587_470) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_587_470)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_587_470
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨587⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨587⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide +kernel) (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(593,470,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_593_470 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_593_470 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (593 : Fin 865)
      exact leaf_4_16_593
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (470 : Fin 865)
      exact leaf_4_16_470
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] fl_4_16_593_470 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_593_470) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_593_470)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_593_470
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨593⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨593⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide +kernel) (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(587,478,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_587_478 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_587_478 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (587 : Fin 865)
      exact leaf_4_16_587
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (478 : Fin 865)
      exact leaf_4_16_478
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] fl_4_16_587_478 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_587_478) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_587_478)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_587_478
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨587⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨587⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide +kernel) (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(596,478,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_596_478 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_596_478 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (596 : Fin 865)
      exact leaf_4_16_596
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (478 : Fin 865)
      exact leaf_4_16_478
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] fl_4_16_596_478 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_596_478) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_596_478)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_596_478
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨596⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨596⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide +kernel) (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(734,270,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_734_270 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_734_270 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (734 : Fin 865)
      exact leaf_4_17_734
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (270 : Fin 865)
      exact leaf_4_17_270
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] fl_4_17_734_270 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_734_270) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_734_270)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_734_270
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨734⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨734⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide +kernel) (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(746,270,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_746_270 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_746_270 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (746 : Fin 865)
      exact leaf_4_17_746
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (270 : Fin 865)
      exact leaf_4_17_270
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] fl_4_17_746_270 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_746_270) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_746_270)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_746_270
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨746⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨746⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide +kernel) (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(734,374,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_734_374 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_734_374 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (734 : Fin 865)
      exact leaf_4_17_734
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (374 : Fin 865)
      exact leaf_4_17_374
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_734_374 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_734_374) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_734_374)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_734_374
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨734⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨734⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide +kernel) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(749,374,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_749_374 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_749_374 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (749 : Fin 865)
      exact leaf_4_17_749
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (374 : Fin 865)
      exact leaf_4_17_374
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_749_374 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_749_374) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_749_374)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_749_374
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨749⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨749⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide +kernel) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(588,471,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_588_471 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_588_471 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (588 : Fin 865)
      exact leaf_4_17_588
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (471 : Fin 865)
      exact leaf_4_17_471
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_588_471 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_588_471) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_588_471)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_588_471
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide +kernel) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(746,471,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_746_471 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_746_471 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (746 : Fin 865)
      exact leaf_4_17_746
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (471 : Fin 865)
      exact leaf_4_17_471
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_746_471 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_746_471) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_746_471)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_746_471
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨746⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨746⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide +kernel) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(588,479,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_588_479 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_588_479 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (588 : Fin 865)
      exact leaf_4_17_588
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (479 : Fin 865)
      exact leaf_4_17_479
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] fl_4_17_588_479 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_588_479) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_588_479)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_588_479
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide +kernel) (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(749,479,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_749_479 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_749_479 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (749 : Fin 865)
      exact leaf_4_17_749
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (479 : Fin 865)
      exact leaf_4_17_479
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] fl_4_17_749_479 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_749_479) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_749_479)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_749_479
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨749⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨749⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide +kernel) (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(623,298,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_623_298 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_623_298 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (623 : Fin 865)
      exact leaf_4_18_623
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (298 : Fin 865)
      exact leaf_4_18_298
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] fl_4_18_623_298 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_623_298) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_623_298)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_623_298
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨623⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨623⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide +kernel) (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(635,298,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_635_298 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_635_298 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (635 : Fin 865)
      exact leaf_4_18_635
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (298 : Fin 865)
      exact leaf_4_18_298
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] fl_4_18_635_298 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_635_298) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_635_298)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_635_298
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨635⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨635⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide +kernel) (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(623,350,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_623_350 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_623_350 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (623 : Fin 865)
      exact leaf_4_18_623
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (350 : Fin 865)
      exact leaf_4_18_350
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_623_350 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_623_350) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_623_350)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_623_350
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨623⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨623⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide +kernel) (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(638,350,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_638_350 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_638_350 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (638 : Fin 865)
      exact leaf_4_18_638
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (350 : Fin 865)
      exact leaf_4_18_350
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_638_350 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_638_350) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_638_350)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_638_350
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨638⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨638⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide +kernel) (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(629,438,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_629_438 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_629_438 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (629 : Fin 865)
      exact leaf_4_18_629
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (438 : Fin 865)
      exact leaf_4_18_438
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_629_438 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_629_438) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_629_438)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_629_438
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨629⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨629⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide +kernel) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(635,438,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_635_438 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_635_438 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (635 : Fin 865)
      exact leaf_4_18_635
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (438 : Fin 865)
      exact leaf_4_18_438
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_635_438 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_635_438) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_635_438)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_635_438
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨635⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨635⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide +kernel) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
