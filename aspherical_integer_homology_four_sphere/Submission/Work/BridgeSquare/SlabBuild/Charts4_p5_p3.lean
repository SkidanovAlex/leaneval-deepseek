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

/-- The chart identity of the flag `(669,463,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_669_463 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_669_463 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (669 : Fin 865)
      exact leaf_4_24_669
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (463 : Fin 865)
      exact leaf_4_24_463
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_669_463 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_669_463) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_669_463)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_669_463
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨669⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨669⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide +kernel) (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(818,463,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_818_463 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_818_463 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (818 : Fin 865)
      exact leaf_4_24_818
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (463 : Fin 865)
      exact leaf_4_24_463
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_818_463 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_818_463) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_818_463)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_818_463
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨818⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨818⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide +kernel) (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(735,271,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_735_271 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_735_271 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (735 : Fin 865)
      exact leaf_4_25_735
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (271 : Fin 865)
      exact leaf_4_25_271
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] fl_4_25_735_271 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_735_271) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_735_271)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_735_271
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨735⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨735⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide +kernel) (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(764,271,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_764_271 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_764_271 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (764 : Fin 865)
      exact leaf_4_25_764
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (271 : Fin 865)
      exact leaf_4_25_271
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] fl_4_25_764_271 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_764_271) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_764_271)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_764_271
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨764⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨764⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide +kernel) (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(735,375,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_735_375 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_735_375 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (735 : Fin 865)
      exact leaf_4_25_735
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (375 : Fin 865)
      exact leaf_4_25_375
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] fl_4_25_735_375 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_735_375) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_735_375)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_735_375
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨735⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨735⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide +kernel) (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w



end

end Work.BridgeSquare.SlabBuild
