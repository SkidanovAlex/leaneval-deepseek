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



end

end Work.BridgeSquare.SlabBuild
