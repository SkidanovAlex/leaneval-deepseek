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


end

end Work.BridgeSquare.SlabBuild
