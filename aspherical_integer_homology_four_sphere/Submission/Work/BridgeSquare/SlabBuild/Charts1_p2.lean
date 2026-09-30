import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts1_p1

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

/-- The chart identity of the flag `(615,304,52)` of the square `5` of cusp `1`. -/
theorem ch_1_5_615_304 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_304))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 5 := by
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
      (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 5 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 5 (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_5_615_304 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (615 : Fin 865)
      exact leaf_1_5_615
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (304 : Fin 865)
      exact leaf_1_5_304
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (52 : Fin 865)
      exact leaf_1_5_52
  have hchart := cSimp_eq_chiRep 1 (a := 5) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_1_5_615_304 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_5_615_304) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (52 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_5_615_304)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_304) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨52⟩ : QbarCW.Cell) fl_1_5_615_304
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨615⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨615⟩ : QbarCell) < (⟨304⟩ : QbarCell) from by decide +kernel) (show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_304))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_304) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_304) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(615,316,52)` of the square `5` of cusp `1`. -/
theorem ch_1_5_615_316 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_316))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 5 := by
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
      (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 5 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 5 (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_5_615_316 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (615 : Fin 865)
      exact leaf_1_5_615
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (316 : Fin 865)
      exact leaf_1_5_316
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (52 : Fin 865)
      exact leaf_1_5_52
  have hchart := cSimp_eq_chiRep 1 (a := 5) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_1_5_615_316 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_5_615_316) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (52 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_5_615_316)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_316) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨52⟩ : QbarCW.Cell) fl_1_5_615_316
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨615⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨615⟩ : QbarCell) < (⟨316⟩ : QbarCell) from by decide +kernel) (show (⟨316⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨316⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_316))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_316) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_615_316) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(654,316,52)` of the square `5` of cusp `1`. -/
theorem ch_1_5_654_316 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_316))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 5 := by
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
      (slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 5 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 5 (slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_5_654_316 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (654 : Fin 865)
      exact leaf_1_5_654
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (316 : Fin 865)
      exact leaf_1_5_316
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (52 : Fin 865)
      exact leaf_1_5_52
  have hchart := cSimp_eq_chiRep 1 (a := 5) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_1_5_654_316 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_5_654_316) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (52 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_5_654_316)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_316) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨52⟩ : QbarCW.Cell) fl_1_5_654_316
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨654⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨654⟩ : QbarCell) < (⟨316⟩ : QbarCell) from by decide +kernel) (show (⟨316⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨316⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_316))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_316) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_316) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(594,320,52)` of the square `5` of cusp `1`. -/
theorem ch_1_5_594_320 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_320))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 5 := by
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
      (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 5 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 5 (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_5_594_320 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (594 : Fin 865)
      exact leaf_1_5_594
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (320 : Fin 865)
      exact leaf_1_5_320
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (52 : Fin 865)
      exact leaf_1_5_52
  have hchart := cSimp_eq_chiRep 1 (a := 5) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_1_5_594_320 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_5_594_320) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (52 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_5_594_320)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_320) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨52⟩ : QbarCW.Cell) fl_1_5_594_320
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨594⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨594⟩ : QbarCell) < (⟨320⟩ : QbarCell) from by decide +kernel) (show (⟨320⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨320⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_320))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_320) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_320) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(636,320,52)` of the square `5` of cusp `1`. -/
theorem ch_1_5_636_320 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_320))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 5 := by
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
      (slabL 1 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 5 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 5 (slabL 1 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_5_636_320 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (636 : Fin 865)
      exact leaf_1_5_636
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (320 : Fin 865)
      exact leaf_1_5_320
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (52 : Fin 865)
      exact leaf_1_5_52
  have hchart := cSimp_eq_chiRep 1 (a := 5) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_1_5_636_320 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_5_636_320) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (52 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_5_636_320)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_320) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨52⟩ : QbarCW.Cell) fl_1_5_636_320
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨636⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨636⟩ : QbarCell) < (⟨320⟩ : QbarCell) from by decide +kernel) (show (⟨320⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨320⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_320))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_320) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_320) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(783,268,45)` of the square `6` of cusp `1`. -/
theorem ch_1_6_783_268 :
    cChain 1 (slabV 1 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_268))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 6 := by
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
      (slabL 1 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 6 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 6 (slabL 1 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_6_783_268 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (783 : Fin 865)
      exact leaf_1_6_783
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (268 : Fin 865)
      exact leaf_1_6_268
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (45 : Fin 865)
      exact leaf_1_6_45
  have hchart := cSimp_eq_chiRep 1 (a := 6) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_1_6_783_268 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_6_783_268) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (45 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_6_783_268)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_268) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨45⟩ : QbarCW.Cell) fl_1_6_783_268
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨783⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨783⟩ : QbarCell) < (⟨268⟩ : QbarCell) from by decide +kernel) (show (⟨268⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨268⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_268))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_268) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_268) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(798,268,45)` of the square `6` of cusp `1`. -/
theorem ch_1_6_798_268 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_268))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 6 := by
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
      (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 6 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 6 (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_6_798_268 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (798 : Fin 865)
      exact leaf_1_6_798
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (268 : Fin 865)
      exact leaf_1_6_268
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (45 : Fin 865)
      exact leaf_1_6_45
  have hchart := cSimp_eq_chiRep 1 (a := 6) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_1_6_798_268 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_6_798_268) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (45 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_6_798_268)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_268) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨45⟩ : QbarCW.Cell) fl_1_6_798_268
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨798⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨798⟩ : QbarCell) < (⟨268⟩ : QbarCell) from by decide +kernel) (show (⟨268⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨268⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_268))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_268) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_268) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(747,272,45)` of the square `6` of cusp `1`. -/
theorem ch_1_6_747_272 :
    cChain 1 (slabV 1 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_272))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 6 := by
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
      (slabL 1 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 6 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 6 (slabL 1 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_6_747_272 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (747 : Fin 865)
      exact leaf_1_6_747
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (272 : Fin 865)
      exact leaf_1_6_272
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (45 : Fin 865)
      exact leaf_1_6_45
  have hchart := cSimp_eq_chiRep 1 (a := 6) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_1_6_747_272 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_6_747_272) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (45 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_6_747_272)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_272) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨45⟩ : QbarCW.Cell) fl_1_6_747_272
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨747⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨747⟩ : QbarCell) < (⟨272⟩ : QbarCell) from by decide +kernel) (show (⟨272⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨272⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_272))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_272) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_272) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(765,272,45)` of the square `6` of cusp `1`. -/
theorem ch_1_6_765_272 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_272))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 6 := by
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
      (slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 6 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 6 (slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_6_765_272 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (765 : Fin 865)
      exact leaf_1_6_765
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (272 : Fin 865)
      exact leaf_1_6_272
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (45 : Fin 865)
      exact leaf_1_6_45
  have hchart := cSimp_eq_chiRep 1 (a := 6) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_1_6_765_272 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_6_765_272) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (45 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_6_765_272)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_272) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨45⟩ : QbarCW.Cell) fl_1_6_765_272
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨765⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨765⟩ : QbarCell) < (⟨272⟩ : QbarCell) from by decide +kernel) (show (⟨272⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨272⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_272))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_272) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_272) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(765,284,45)` of the square `6` of cusp `1`. -/
theorem ch_1_6_765_284 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_284))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 6 := by
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
      (slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 6 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 6 (slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_6_765_284 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (765 : Fin 865)
      exact leaf_1_6_765
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (284 : Fin 865)
      exact leaf_1_6_284
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (45 : Fin 865)
      exact leaf_1_6_45
  have hchart := cSimp_eq_chiRep 1 (a := 6) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_1_6_765_284 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_6_765_284) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (45 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_6_765_284)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_284) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨45⟩ : QbarCW.Cell) fl_1_6_765_284
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨765⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨765⟩ : QbarCell) < (⟨284⟩ : QbarCell) from by decide +kernel) (show (⟨284⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨284⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_284))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_284) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_765_284) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(798,284,45)` of the square `6` of cusp `1`. -/
theorem ch_1_6_798_284 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_284))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 6 := by
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
      (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 6 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 6 (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_6_798_284 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (798 : Fin 865)
      exact leaf_1_6_798
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (284 : Fin 865)
      exact leaf_1_6_284
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (45 : Fin 865)
      exact leaf_1_6_45
  have hchart := cSimp_eq_chiRep 1 (a := 6) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_1_6_798_284 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_6_798_284) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (45 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_6_798_284)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_284) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨45⟩ : QbarCW.Cell) fl_1_6_798_284
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨798⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨798⟩ : QbarCell) < (⟨284⟩ : QbarCell) from by decide +kernel) (show (⟨284⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨284⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_284))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_284) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_798_284) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(747,288,45)` of the square `6` of cusp `1`. -/
theorem ch_1_6_747_288 :
    cChain 1 (slabV 1 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_288))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 6 := by
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
      (slabL 1 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 6 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 6 (slabL 1 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_6_747_288 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (747 : Fin 865)
      exact leaf_1_6_747
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (288 : Fin 865)
      exact leaf_1_6_288
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (45 : Fin 865)
      exact leaf_1_6_45
  have hchart := cSimp_eq_chiRep 1 (a := 6) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_1_6_747_288 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_6_747_288) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (45 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_6_747_288)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_288) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨45⟩ : QbarCW.Cell) fl_1_6_747_288
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨747⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨747⟩ : QbarCell) < (⟨288⟩ : QbarCell) from by decide +kernel) (show (⟨288⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨288⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_288))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_288) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_747_288) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(783,288,45)` of the square `6` of cusp `1`. -/
theorem ch_1_6_783_288 :
    cChain 1 (slabV 1 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_288))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 6 := by
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
      (slabL 1 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 6 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 6 (slabL 1 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_6_783_288 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (783 : Fin 865)
      exact leaf_1_6_783
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (288 : Fin 865)
      exact leaf_1_6_288
    · show Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (45 : Fin 865)
      exact leaf_1_6_45
  have hchart := cSimp_eq_chiRep 1 (a := 6) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_1_6_783_288 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_6_783_288) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (45 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_6_783_288)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_288) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨45⟩ : QbarCW.Cell) fl_1_6_783_288
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨783⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨783⟩ : QbarCell) < (⟨288⟩ : QbarCell) from by decide +kernel) (show (⟨288⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨288⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_288))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_288) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨147, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (45 : Fin 865)) fl_1_6_783_288) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(711,236,38)` of the square `7` of cusp `1`. -/
theorem ch_1_7_711_236 :
    cChain 1 (slabV 1 ![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_236))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 7 := by
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
      (slabL 1 (![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 7 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 7 (slabL 1 (![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_7_711_236 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (711 : Fin 865)
      exact leaf_1_7_711
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (236 : Fin 865)
      exact leaf_1_7_236
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (38 : Fin 865)
      exact leaf_1_7_38
  have hchart := cSimp_eq_chiRep 1 (a := 7) rfl
    ![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] fl_1_7_711_236 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_7_711_236) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (38 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_7_711_236)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_236) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨38⟩ : QbarCW.Cell) fl_1_7_711_236
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨711⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨711⟩ : QbarCell) < (⟨236⟩ : QbarCell) from by decide +kernel) (show (⟨236⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨236⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_236))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_236) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_236) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(726,236,38)` of the square `7` of cusp `1`. -/
theorem ch_1_7_726_236 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_236))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 7 := by
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
      (slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 7 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 7 (slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_7_726_236 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (726 : Fin 865)
      exact leaf_1_7_726
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (236 : Fin 865)
      exact leaf_1_7_236
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (38 : Fin 865)
      exact leaf_1_7_38
  have hchart := cSimp_eq_chiRep 1 (a := 7) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ] fl_1_7_726_236 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_7_726_236) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (38 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_7_726_236)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_236) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨38⟩ : QbarCW.Cell) fl_1_7_726_236
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨726⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨726⟩ : QbarCell) < (⟨236⟩ : QbarCell) from by decide +kernel) (show (⟨236⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨236⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_236))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_236) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_236) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(675,240,38)` of the square `7` of cusp `1`. -/
theorem ch_1_7_675_240 :
    cChain 1 (slabV 1 ![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_240))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 7 := by
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
      (slabL 1 (![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 7 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 7 (slabL 1 (![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_7_675_240 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (675 : Fin 865)
      exact leaf_1_7_675
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (240 : Fin 865)
      exact leaf_1_7_240
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (38 : Fin 865)
      exact leaf_1_7_38
  have hchart := cSimp_eq_chiRep 1 (a := 7) rfl
    ![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] fl_1_7_675_240 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_7_675_240) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (38 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_7_675_240)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_240) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨38⟩ : QbarCW.Cell) fl_1_7_675_240
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨675⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨675⟩ : QbarCell) < (⟨240⟩ : QbarCell) from by decide +kernel) (show (⟨240⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨240⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_240))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_240) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_240) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(693,240,38)` of the square `7` of cusp `1`. -/
theorem ch_1_7_693_240 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_240))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 7 := by
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
      (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 7 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 7 (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_7_693_240 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (693 : Fin 865)
      exact leaf_1_7_693
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (240 : Fin 865)
      exact leaf_1_7_240
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (38 : Fin 865)
      exact leaf_1_7_38
  have hchart := cSimp_eq_chiRep 1 (a := 7) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] fl_1_7_693_240 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_7_693_240) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (38 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_7_693_240)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_240) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨38⟩ : QbarCW.Cell) fl_1_7_693_240
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨693⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨693⟩ : QbarCell) < (⟨240⟩ : QbarCell) from by decide +kernel) (show (⟨240⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨240⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_240))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_240) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_240) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(693,252,38)` of the square `7` of cusp `1`. -/
theorem ch_1_7_693_252 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_252))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 7 := by
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
      (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 7 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 7 (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_7_693_252 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (693 : Fin 865)
      exact leaf_1_7_693
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (252 : Fin 865)
      exact leaf_1_7_252
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (38 : Fin 865)
      exact leaf_1_7_38
  have hchart := cSimp_eq_chiRep 1 (a := 7) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_1_7_693_252 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_7_693_252) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (38 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_7_693_252)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_252) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨38⟩ : QbarCW.Cell) fl_1_7_693_252
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨693⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨693⟩ : QbarCell) < (⟨252⟩ : QbarCell) from by decide +kernel) (show (⟨252⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨252⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_252))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_252) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_693_252) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(726,252,38)` of the square `7` of cusp `1`. -/
theorem ch_1_7_726_252 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_252))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 7 := by
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
      (slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 7 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 7 (slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_7_726_252 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (726 : Fin 865)
      exact leaf_1_7_726
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (252 : Fin 865)
      exact leaf_1_7_252
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (38 : Fin 865)
      exact leaf_1_7_38
  have hchart := cSimp_eq_chiRep 1 (a := 7) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_1_7_726_252 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_7_726_252) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (38 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_7_726_252)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_252) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨38⟩ : QbarCW.Cell) fl_1_7_726_252
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨726⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨726⟩ : QbarCell) < (⟨252⟩ : QbarCell) from by decide +kernel) (show (⟨252⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨252⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_252))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_252) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_726_252) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(675,256,38)` of the square `7` of cusp `1`. -/
theorem ch_1_7_675_256 :
    cChain 1 (slabV 1 ![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_256))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 7 := by
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
      (slabL 1 (![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 7 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 7 (slabL 1 (![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_7_675_256 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (675 : Fin 865)
      exact leaf_1_7_675
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (256 : Fin 865)
      exact leaf_1_7_256
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (38 : Fin 865)
      exact leaf_1_7_38
  have hchart := cSimp_eq_chiRep 1 (a := 7) rfl
    ![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_1_7_675_256 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_7_675_256) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (38 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_7_675_256)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_256) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨38⟩ : QbarCW.Cell) fl_1_7_675_256
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨675⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨675⟩ : QbarCell) < (⟨256⟩ : QbarCell) from by decide +kernel) (show (⟨256⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨256⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_256))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_256) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_675_256) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(711,256,38)` of the square `7` of cusp `1`. -/
theorem ch_1_7_711_256 :
    cChain 1 (slabV 1 ![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_256))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 7 := by
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
      (slabL 1 (![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 7 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 7 (slabL 1 (![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_7_711_256 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (711 : Fin 865)
      exact leaf_1_7_711
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (256 : Fin 865)
      exact leaf_1_7_256
    · show Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (38 : Fin 865)
      exact leaf_1_7_38
  have hchart := cSimp_eq_chiRep 1 (a := 7) rfl
    ![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_1_7_711_256 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_7_711_256) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (38 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_7_711_256)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_256) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨38⟩ : QbarCW.Cell) fl_1_7_711_256
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨711⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨711⟩ : QbarCell) < (⟨256⟩ : QbarCell) from by decide +kernel) (show (⟨256⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨256⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_256))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_256) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨5, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (38 : Fin 865)) fl_1_7_711_256) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

end

end Work.BridgeSquare.SlabBuild
