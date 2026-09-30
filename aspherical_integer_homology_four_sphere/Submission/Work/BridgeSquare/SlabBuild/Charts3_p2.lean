import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts3_p1

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

/-- The chart identity of the flag `(642,536,164)` of the square `13` of cusp `3`. -/
theorem ch_3_13_642_536 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_536))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 13 := by
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
      (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 13 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 13 (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_13_642_536 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (642 : Fin 865)
      exact leaf_3_13_642
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (536 : Fin 865)
      exact leaf_3_13_536
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (164 : Fin 865)
      exact leaf_3_13_164
  have hchart := cSimp_eq_chiRep 3 (a := 13) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_3_13_642_536 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_13_642_536) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (164 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_13_642_536)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_536) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨164⟩ : QbarCW.Cell) fl_3_13_642_536
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨642⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨642⟩ : QbarCell) < (⟨536⟩ : QbarCell) from by decide +kernel) (show (⟨536⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨536⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_536))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_536) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_536) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(642,572,164)` of the square `13` of cusp `3`. -/
theorem ch_3_13_642_572 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_572))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 13 := by
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
      (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 13 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 13 (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_13_642_572 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (642 : Fin 865)
      exact leaf_3_13_642
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (572 : Fin 865)
      exact leaf_3_13_572
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (164 : Fin 865)
      exact leaf_3_13_164
  have hchart := cSimp_eq_chiRep 3 (a := 13) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_3_13_642_572 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_13_642_572) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (164 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_13_642_572)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_572) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨164⟩ : QbarCW.Cell) fl_3_13_642_572
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨642⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨642⟩ : QbarCell) < (⟨572⟩ : QbarCell) from by decide +kernel) (show (⟨572⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨572⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_572))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_572) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_642_572) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(789,572,164)` of the square `13` of cusp `3`. -/
theorem ch_3_13_789_572 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_572))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 13 := by
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
      (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 13 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 13 (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_13_789_572 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (789 : Fin 865)
      exact leaf_3_13_789
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (572 : Fin 865)
      exact leaf_3_13_572
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (164 : Fin 865)
      exact leaf_3_13_164
  have hchart := cSimp_eq_chiRep 3 (a := 13) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_3_13_789_572 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_13_789_572) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (164 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_13_789_572)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_572) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨164⟩ : QbarCW.Cell) fl_3_13_789_572
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨789⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨789⟩ : QbarCell) < (⟨572⟩ : QbarCell) from by decide +kernel) (show (⟨572⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨572⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_572))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_572) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_572) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(600,576,164)` of the square `13` of cusp `3`. -/
theorem ch_3_13_600_576 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_576))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 13 := by
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
      (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 13 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 13 (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_13_600_576 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (600 : Fin 865)
      exact leaf_3_13_600
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (576 : Fin 865)
      exact leaf_3_13_576
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (164 : Fin 865)
      exact leaf_3_13_164
  have hchart := cSimp_eq_chiRep 3 (a := 13) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_3_13_600_576 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_13_600_576) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (164 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_13_600_576)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_576) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨164⟩ : QbarCW.Cell) fl_3_13_600_576
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨600⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨600⟩ : QbarCell) < (⟨576⟩ : QbarCell) from by decide +kernel) (show (⟨576⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨576⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_576))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_576) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_576) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(753,576,164)` of the square `13` of cusp `3`. -/
theorem ch_3_13_753_576 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_576))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 13 := by
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
      (slabL 3 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 13 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 13 (slabL 3 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_13_753_576 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (753 : Fin 865)
      exact leaf_3_13_753
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (576 : Fin 865)
      exact leaf_3_13_576
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (164 : Fin 865)
      exact leaf_3_13_164
  have hchart := cSimp_eq_chiRep 3 (a := 13) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_3_13_753_576 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_13_753_576) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (164 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_13_753_576)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_576) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨164⟩ : QbarCW.Cell) fl_3_13_753_576
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨753⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨753⟩ : QbarCell) < (⟨576⟩ : QbarCell) from by decide +kernel) (show (⟨576⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨576⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_576))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_576) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_576) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(822,516,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_822_516 :
    cChain 3 (slabV 3 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_822_516 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (822 : Fin 865)
      exact leaf_3_14_822
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (516 : Fin 865)
      exact leaf_3_14_516
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_3_14_822_516 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_822_516) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_822_516)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_822_516
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨822⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨822⟩ : QbarCell) < (⟨516⟩ : QbarCell) from by decide +kernel) (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(852,516,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_852_516 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_852_516 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (852 : Fin 865)
      exact leaf_3_14_852
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (516 : Fin 865)
      exact leaf_3_14_516
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_3_14_852_516 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_852_516) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_852_516)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_852_516
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨852⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨852⟩ : QbarCell) < (⟨516⟩ : QbarCell) from by decide +kernel) (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(681,532,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_681_532 :
    cChain 3 (slabV 3 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_681_532 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (681 : Fin 865)
      exact leaf_3_14_681
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (532 : Fin 865)
      exact leaf_3_14_532
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_3_14_681_532 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_681_532) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_681_532)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_681_532
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨681⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨681⟩ : QbarCell) < (⟨532⟩ : QbarCell) from by decide +kernel) (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(717,532,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_717_532 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_717_532 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (717 : Fin 865)
      exact leaf_3_14_717
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (532 : Fin 865)
      exact leaf_3_14_532
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_3_14_717_532 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_717_532) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_717_532)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_717_532
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨717⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨717⟩ : QbarCell) < (⟨532⟩ : QbarCell) from by decide +kernel) (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(717,564,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_717_564 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_717_564 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (717 : Fin 865)
      exact leaf_3_14_717
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (564 : Fin 865)
      exact leaf_3_14_564
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_3_14_717_564 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_717_564) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_717_564)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_717_564
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨717⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨717⟩ : QbarCell) < (⟨564⟩ : QbarCell) from by decide +kernel) (show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(852,564,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_852_564 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_564))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_852_564 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (852 : Fin 865)
      exact leaf_3_14_852
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (564 : Fin 865)
      exact leaf_3_14_564
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_3_14_852_564 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_852_564) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_852_564)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_564) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_852_564
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨852⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨852⟩ : QbarCell) < (⟨564⟩ : QbarCell) from by decide +kernel) (show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_564))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_564) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_564) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(681,568,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_681_568 :
    cChain 3 (slabV 3 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_568))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_681_568 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (681 : Fin 865)
      exact leaf_3_14_681
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (568 : Fin 865)
      exact leaf_3_14_568
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_3_14_681_568 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_681_568) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_681_568)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_568) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_681_568
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨681⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨681⟩ : QbarCell) < (⟨568⟩ : QbarCell) from by decide +kernel) (show (⟨568⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨568⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_568))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_568) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_568) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(822,568,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_822_568 :
    cChain 3 (slabV 3 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_568))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_822_568 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (822 : Fin 865)
      exact leaf_3_14_822
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (568 : Fin 865)
      exact leaf_3_14_568
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_3_14_822_568 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_822_568) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_822_568)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_568) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_822_568
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨822⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨822⟩ : QbarCell) < (⟨568⟩ : QbarCell) from by decide +kernel) (show (⟨568⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨568⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_568))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_568) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_568) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(771,488,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_771_488 :
    cChain 3 (slabV 3 ![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_488))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_771_488 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (771 : Fin 865)
      exact leaf_3_15_771
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (488 : Fin 865)
      exact leaf_3_15_488
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_771_488 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_771_488) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_771_488)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_488) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_771_488
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨771⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨771⟩ : QbarCell) < (⟨488⟩ : QbarCell) from by decide +kernel) (show (⟨488⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨488⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_488))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_488) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_488) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(804,488,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_804_488 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_488))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_804_488 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (804 : Fin 865)
      exact leaf_3_15_804
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (488 : Fin 865)
      exact leaf_3_15_488
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_804_488 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_804_488) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_804_488)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_488) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_804_488
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨804⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨804⟩ : QbarCell) < (⟨488⟩ : QbarCell) from by decide +kernel) (show (⟨488⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨488⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_488))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_488) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_488) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(621,504,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_621_504 :
    cChain 3 (slabV 3 ![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_621_504 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (621 : Fin 865)
      exact leaf_3_15_621
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (504 : Fin 865)
      exact leaf_3_15_504
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_621_504 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_621_504) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_621_504)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_621_504
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨621⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨621⟩ : QbarCell) < (⟨504⟩ : QbarCell) from by decide +kernel) (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(660,504,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_660_504 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_660_504 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (660 : Fin 865)
      exact leaf_3_15_660
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (504 : Fin 865)
      exact leaf_3_15_504
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_660_504 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_660_504) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_660_504)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_660_504
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨660⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨660⟩ : QbarCell) < (⟨504⟩ : QbarCell) from by decide +kernel) (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(660,556,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_660_556 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_660_556 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (660 : Fin 865)
      exact leaf_3_15_660
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (556 : Fin 865)
      exact leaf_3_15_556
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_660_556 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_660_556) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_660_556)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_660_556
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨660⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨660⟩ : QbarCell) < (⟨556⟩ : QbarCell) from by decide +kernel) (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(804,556,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_804_556 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_804_556 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (804 : Fin 865)
      exact leaf_3_15_804
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (556 : Fin 865)
      exact leaf_3_15_556
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_804_556 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_804_556) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_804_556)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_804_556
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨804⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨804⟩ : QbarCell) < (⟨556⟩ : QbarCell) from by decide +kernel) (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(621,560,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_621_560 :
    cChain 3 (slabV 3 ![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_621_560 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (621 : Fin 865)
      exact leaf_3_15_621
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (560 : Fin 865)
      exact leaf_3_15_560
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_621_560 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_621_560) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_621_560)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_621_560
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨621⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨621⟩ : QbarCell) < (⟨560⟩ : QbarCell) from by decide +kernel) (show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(771,560,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_771_560 :
    cChain 3 (slabV 3 ![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_560))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_771_560 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (771 : Fin 865)
      exact leaf_3_15_771
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (560 : Fin 865)
      exact leaf_3_15_560
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_771_560 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_771_560) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_771_560)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_560) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_771_560
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨771⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨771⟩ : QbarCell) < (⟨560⟩ : QbarCell) from by decide +kernel) (show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_560))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_560) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_771_560) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

end

end Work.BridgeSquare.SlabBuild
