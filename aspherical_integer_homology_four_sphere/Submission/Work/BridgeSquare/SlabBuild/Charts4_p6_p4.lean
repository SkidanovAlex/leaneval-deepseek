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

/-- The chart identity of the flag `(692,239,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_692_239 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_692_239 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (692 : Fin 865)
      exact leaf_4_31_692
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (239 : Fin 865)
      exact leaf_4_31_239
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_692_239 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_692_239) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_692_239)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_692_239
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨692⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨692⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide +kernel) (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(663,395,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_663_395 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_663_395 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (663 : Fin 865)
      exact leaf_4_31_663
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (395 : Fin 865)
      exact leaf_4_31_395
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_663_395 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_663_395) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_663_395)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_663_395
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨663⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨663⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide +kernel) (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(695,395,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_695_395 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_695_395 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (695 : Fin 865)
      exact leaf_4_31_695
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (395 : Fin 865)
      exact leaf_4_31_395
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_695_395 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_695_395) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_695_395)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_695_395
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨695⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨695⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide +kernel) (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(686,450,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_686_450 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_686_450 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (686 : Fin 865)
      exact leaf_4_31_686
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (450 : Fin 865)
      exact leaf_4_31_450
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_686_450 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_686_450) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_686_450)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_686_450
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨686⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨686⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide +kernel) (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(692,450,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_692_450 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_692_450 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (692 : Fin 865)
      exact leaf_4_31_692
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (450 : Fin 865)
      exact leaf_4_31_450
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_692_450 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_692_450) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_692_450)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_692_450
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨692⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨692⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide +kernel) (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w



end

end Work.BridgeSquare.SlabBuild
