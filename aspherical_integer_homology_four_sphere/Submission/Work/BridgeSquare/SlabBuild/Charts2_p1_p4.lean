import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts2_p1_p1
import Submission.Work.BridgeSquare.SlabBuild.Charts2_p1_p2

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

/-- The chart identity of the flag `(861,428,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_861_428 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_861_428 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (861 : Fin 865)
      exact leaf_2_8_861
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (428 : Fin 865)
      exact leaf_2_8_428
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_2_8_861_428 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_861_428) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_861_428)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_861_428
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨861⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨861⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide +kernel) (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(657,444,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_657_444 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_657_444 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (657 : Fin 865)
      exact leaf_2_8_657
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (444 : Fin 865)
      exact leaf_2_8_444
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_2_8_657_444 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_657_444) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_657_444)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_657_444
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨657⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨657⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide +kernel) (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(801,444,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_801_444 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_801_444 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (801 : Fin 865)
      exact leaf_2_8_801
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (444 : Fin 865)
      exact leaf_2_8_444
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_2_8_801_444 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_801_444) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_801_444)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_801_444
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨801⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨801⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide +kernel) (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(768,388,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_768_388 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_768_388 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (768 : Fin 865)
      exact leaf_2_9_768
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (388 : Fin 865)
      exact leaf_2_9_388
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_2_9_768_388 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_768_388) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_768_388)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_768_388
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨768⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨768⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide +kernel) (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(834,388,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_834_388 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_834_388 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (834 : Fin 865)
      exact leaf_2_9_834
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (388 : Fin 865)
      exact leaf_2_9_388
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_2_9_834_388 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_834_388) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_834_388)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_834_388
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨834⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨834⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide +kernel) (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w



end

end Work.BridgeSquare.SlabBuild
