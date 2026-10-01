import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts2_p1

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

/-- The chart identity of the flag `(696,412,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_696_412 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_696_412 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (696 : Fin 865)
      exact leaf_2_9_696
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (412 : Fin 865)
      exact leaf_2_9_412
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_2_9_696_412 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_696_412) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_696_412)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_696_412
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨696⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨696⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide +kernel) (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(696,460,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_696_460 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_696_460 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (696 : Fin 865)
      exact leaf_2_9_696
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (460 : Fin 865)
      exact leaf_2_9_460
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_2_9_696_460 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_696_460) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_696_460)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_696_460
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨696⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨696⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide +kernel) (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(834,460,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_834_460 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_834_460 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (834 : Fin 865)
      exact leaf_2_9_834
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (460 : Fin 865)
      exact leaf_2_9_460
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_2_9_834_460 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_834_460) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_834_460)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_834_460
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨834⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨834⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide +kernel) (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(618,476,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_618_476 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_618_476 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (618 : Fin 865)
      exact leaf_2_9_618
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (476 : Fin 865)
      exact leaf_2_9_476
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_2_9_618_476 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_618_476) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_618_476)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_618_476
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨618⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨618⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide +kernel) (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(768,476,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_768_476 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_768_476 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (768 : Fin 865)
      exact leaf_2_9_768
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (476 : Fin 865)
      exact leaf_2_9_476
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_2_9_768_476 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_768_476) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_768_476)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_768_476
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨768⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨768⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide +kernel) (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
