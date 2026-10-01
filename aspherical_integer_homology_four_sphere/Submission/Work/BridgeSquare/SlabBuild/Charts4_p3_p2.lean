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



end

end Work.BridgeSquare.SlabBuild
