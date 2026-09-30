import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts0_p1

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

/-- The chart identity of the flag `(651,292,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_651_292 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_651_292 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (651 : Fin 865)
      exact leaf_0_1_651
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (292 : Fin 865)
      exact leaf_0_1_292
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_0_1_651_292 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_651_292) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_651_292)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_651_292
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨651⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨651⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide +kernel) (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(651,356,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_651_356 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_651_356 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (651 : Fin 865)
      exact leaf_0_1_651
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (356 : Fin 865)
      exact leaf_0_1_356
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_0_1_651_356 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_651_356) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_651_356)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_651_356
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨651⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨651⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide +kernel) (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(723,356,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_723_356 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_723_356 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (723 : Fin 865)
      exact leaf_0_1_723
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (356 : Fin 865)
      exact leaf_0_1_356
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_0_1_723_356 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_723_356) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_723_356)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_723_356
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨723⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨723⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide +kernel) (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(633,360,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_633_360 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_633_360 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (633 : Fin 865)
      exact leaf_0_1_633
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (360 : Fin 865)
      exact leaf_0_1_360
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_0_1_633_360 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_633_360) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_633_360)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_633_360
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨633⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨633⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide +kernel) (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(708,360,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_708_360 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_708_360 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (708 : Fin 865)
      exact leaf_0_1_708
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (360 : Fin 865)
      exact leaf_0_1_360
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_0_1_708_360 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_708_360) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_708_360)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_708_360
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨708⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨708⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide +kernel) (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(672,232,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_672_232 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_672_232 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (672 : Fin 865)
      exact leaf_0_2_672
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (232 : Fin 865)
      exact leaf_0_2_232
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_0_2_672_232 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_672_232) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_672_232)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_672_232
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨672⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨672⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide +kernel) (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(690,232,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_690_232 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_690_232 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (690 : Fin 865)
      exact leaf_0_2_690
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (232 : Fin 865)
      exact leaf_0_2_232
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_0_2_690_232 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_690_232) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_690_232)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_690_232
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨690⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨690⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide +kernel) (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(591,296,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_591_296 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_591_296 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (591 : Fin 865)
      exact leaf_0_2_591
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (296 : Fin 865)
      exact leaf_0_2_296
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_0_2_591_296 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_591_296) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_591_296)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_591_296
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨591⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨591⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide +kernel) (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(612,296,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_612_296 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_612_296 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (612 : Fin 865)
      exact leaf_0_2_612
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (296 : Fin 865)
      exact leaf_0_2_296
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_0_2_612_296 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_612_296) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_612_296)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_612_296
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨612⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨612⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide +kernel) (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(612,404,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_612_404 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_612_404 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (612 : Fin 865)
      exact leaf_0_2_612
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (404 : Fin 865)
      exact leaf_0_2_404
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_0_2_612_404 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_612_404) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_612_404)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_612_404
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨612⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨612⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide +kernel) (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(690,404,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_690_404 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_690_404 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (690 : Fin 865)
      exact leaf_0_2_690
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (404 : Fin 865)
      exact leaf_0_2_404
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_0_2_690_404 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_690_404) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_690_404)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_690_404
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨690⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨690⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide +kernel) (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(591,408,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_591_408 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_591_408 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (591 : Fin 865)
      exact leaf_0_2_591
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (408 : Fin 865)
      exact leaf_0_2_408
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_0_2_591_408 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_591_408) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_591_408)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_591_408
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨591⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨591⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide +kernel) (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(672,408,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_672_408 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_672_408 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (672 : Fin 865)
      exact leaf_0_2_672
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (408 : Fin 865)
      exact leaf_0_2_408
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_0_2_672_408 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_672_408) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_672_408)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_672_408
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨672⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨672⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide +kernel) (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(813,200,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_813_200 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_813_200 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (813 : Fin 865)
      exact leaf_0_3_813
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (200 : Fin 865)
      exact leaf_0_3_200
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_813_200 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_813_200) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_813_200)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_813_200
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨813⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨813⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide +kernel) (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(828,200,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_828_200 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_828_200 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (828 : Fin 865)
      exact leaf_0_3_828
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (200 : Fin 865)
      exact leaf_0_3_200
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_828_200 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_828_200) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_828_200)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_828_200
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨828⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨828⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide +kernel) (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(744,264,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_744_264 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_744_264 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (744 : Fin 865)
      exact leaf_0_3_744
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (264 : Fin 865)
      exact leaf_0_3_264
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_744_264 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_744_264) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_744_264)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_744_264
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨744⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨744⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide +kernel) (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(762,264,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_762_264 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_762_264 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (762 : Fin 865)
      exact leaf_0_3_762
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (264 : Fin 865)
      exact leaf_0_3_264
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_762_264 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_762_264) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_762_264)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_762_264
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨762⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨762⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide +kernel) (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(762,380,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_762_380 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_762_380 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (762 : Fin 865)
      exact leaf_0_3_762
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (380 : Fin 865)
      exact leaf_0_3_380
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_762_380 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_762_380) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_762_380)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_762_380
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨762⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨762⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide +kernel) (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(828,380,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_828_380 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_828_380 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (828 : Fin 865)
      exact leaf_0_3_828
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (380 : Fin 865)
      exact leaf_0_3_380
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_828_380 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_828_380) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_828_380)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_828_380
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨828⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨828⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide +kernel) (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(744,384,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_744_384 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_744_384 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (744 : Fin 865)
      exact leaf_0_3_744
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (384 : Fin 865)
      exact leaf_0_3_384
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_744_384 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_744_384) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_744_384)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_744_384
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨744⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨744⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide +kernel) (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(813,384,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_813_384 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_813_384 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (813 : Fin 865)
      exact leaf_0_3_813
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (384 : Fin 865)
      exact leaf_0_3_384
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_813_384 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_813_384) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_813_384)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_813_384
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨813⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨813⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide +kernel) (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

end

end Work.BridgeSquare.SlabBuild
