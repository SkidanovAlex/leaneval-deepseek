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

/-- The chart identity of the flag `(701,346,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_701_346 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_701_346 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (701 : Fin 865)
      exact leaf_4_27_701
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (346 : Fin 865)
      exact leaf_4_27_346
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] fl_4_27_701_346 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_701_346) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_701_346)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_701_346
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨701⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨701⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide +kernel) (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(713,346,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_713_346 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_713_346 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (713 : Fin 865)
      exact leaf_4_27_713
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (346 : Fin 865)
      exact leaf_4_27_346
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] fl_4_27_713_346 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_713_346) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_713_346)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_713_346
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨713⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨713⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide +kernel) (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(704,422,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_704_422 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_704_422 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (704 : Fin 865)
      exact leaf_4_27_704
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (422 : Fin 865)
      exact leaf_4_27_422
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] fl_4_27_704_422 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_704_422) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_704_422)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_704_422
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨704⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨704⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide +kernel) (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(710,422,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_710_422 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_710_422 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (710 : Fin 865)
      exact leaf_4_27_710
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (422 : Fin 865)
      exact leaf_4_27_422
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] fl_4_27_710_422 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_710_422) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_710_422)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_710_422
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨710⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨710⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide +kernel) (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(704,430,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_704_430 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_704_430 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (704 : Fin 865)
      exact leaf_4_27_704
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (430 : Fin 865)
      exact leaf_4_27_430
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] fl_4_27_704_430 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_704_430) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_704_430)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_704_430
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨704⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨704⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide +kernel) (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(713,430,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_713_430 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_713_430 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (713 : Fin 865)
      exact leaf_4_27_713
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (430 : Fin 865)
      exact leaf_4_27_430
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] fl_4_27_713_430 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_713_430) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_713_430)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_713_430
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨713⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨713⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide +kernel) (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(624,299,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_624_299 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_624_299 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (624 : Fin 865)
      exact leaf_4_28_624
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (299 : Fin 865)
      exact leaf_4_28_299
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_624_299 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_624_299) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_624_299)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_624_299
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨624⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨624⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide +kernel) (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(653,299,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_653_299 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_653_299 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (653 : Fin 865)
      exact leaf_4_28_653
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (299 : Fin 865)
      exact leaf_4_28_299
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_653_299 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_653_299) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_653_299)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_653_299
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨653⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨653⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide +kernel) (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(624,351,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_624_351 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_624_351 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (624 : Fin 865)
      exact leaf_4_28_624
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (351 : Fin 865)
      exact leaf_4_28_351
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_624_351 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_624_351) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_624_351)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_624_351
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨624⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨624⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide +kernel) (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(656,351,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_656_351 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_656_351 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (656 : Fin 865)
      exact leaf_4_28_656
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (351 : Fin 865)
      exact leaf_4_28_351
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_656_351 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_656_351) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_656_351)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_656_351
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨656⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨656⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide +kernel) (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(647,434,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_647_434 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_647_434 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (647 : Fin 865)
      exact leaf_4_28_647
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (434 : Fin 865)
      exact leaf_4_28_434
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_647_434 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_647_434) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_647_434)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_647_434
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨647⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨647⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide +kernel) (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(653,434,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_653_434 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_653_434 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (653 : Fin 865)
      exact leaf_4_28_653
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (434 : Fin 865)
      exact leaf_4_28_434
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_653_434 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_653_434) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_653_434)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_653_434
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨653⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨653⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide +kernel) (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(647,442,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_647_442 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_647_442 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (647 : Fin 865)
      exact leaf_4_28_647
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (442 : Fin 865)
      exact leaf_4_28_442
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_647_442 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_647_442) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_647_442)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_647_442
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨647⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨647⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide +kernel) (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(656,442,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_656_442 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_656_442 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (656 : Fin 865)
      exact leaf_4_28_656
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (442 : Fin 865)
      exact leaf_4_28_442
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_656_442 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_656_442) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_656_442)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_656_442
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨656⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨656⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide +kernel) (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(663,239,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_663_239 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_663_239 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (663 : Fin 865)
      exact leaf_4_31_663
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (239 : Fin 865)
      exact leaf_4_31_239
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_663_239 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_663_239) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_663_239)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_663_239
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨663⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨663⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide +kernel) (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

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

/-- The chart identity of the flag `(686,458,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_686_458 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_686_458 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (686 : Fin 865)
      exact leaf_4_31_686
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (458 : Fin 865)
      exact leaf_4_31_458
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_686_458 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_686_458) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_686_458)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_686_458
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨686⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨686⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide +kernel) (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(695,458,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_695_458 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_695_458 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (695 : Fin 865)
      exact leaf_4_31_695
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (458 : Fin 865)
      exact leaf_4_31_458
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_695_458 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_695_458) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_695_458)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_695_458
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨695⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨695⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide +kernel) (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
