import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts3_p1_p1
import Submission.Work.BridgeSquare.SlabBuild.Charts3_p1_p2

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

/-- Leaf `804` of the square `15` of cusp `3`. -/
theorem leaf_3_15_804 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (804 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- The chart identity of the flag `(837,484,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_837_484 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_837_484 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (837 : Fin 865)
      exact leaf_3_12_837
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (484 : Fin 865)
      exact leaf_3_12_484
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_3_12_837_484 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_837_484) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_837_484)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_837_484
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨837⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨837⟩ : QbarCell) < (⟨484⟩ : QbarCell) from by decide +kernel) (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(864,484,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_864_484 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_864_484 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (864 : Fin 865)
      exact leaf_3_12_864
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (484 : Fin 865)
      exact leaf_3_12_484
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_3_12_864_484 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_864_484) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_864_484)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_864_484
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨864⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨864⟩ : QbarCell) < (⟨484⟩ : QbarCell) from by decide +kernel) (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(699,500,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_699_500 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_699_500 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (699 : Fin 865)
      exact leaf_3_12_699
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (500 : Fin 865)
      exact leaf_3_12_500
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_3_12_699_500 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_699_500) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_699_500)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_699_500
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨699⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨699⟩ : QbarCell) < (⟨500⟩ : QbarCell) from by decide +kernel) (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(732,500,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_732_500 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_732_500 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (732 : Fin 865)
      exact leaf_3_12_732
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (500 : Fin 865)
      exact leaf_3_12_500
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_3_12_732_500 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_732_500) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_732_500)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_732_500
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨732⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨732⟩ : QbarCell) < (⟨500⟩ : QbarCell) from by decide +kernel) (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(732,548,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_732_548 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_732_548 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (732 : Fin 865)
      exact leaf_3_12_732
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (548 : Fin 865)
      exact leaf_3_12_548
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_3_12_732_548 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_732_548) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_732_548)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_732_548
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨732⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨732⟩ : QbarCell) < (⟨548⟩ : QbarCell) from by decide +kernel) (show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w



end

end Work.BridgeSquare.SlabBuild
