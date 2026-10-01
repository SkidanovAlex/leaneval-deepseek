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

/-- The chart identity of the flag `(857,419,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_857_419 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_857_419 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (857 : Fin 865)
      exact leaf_4_44_857
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (419 : Fin 865)
      exact leaf_4_44_419
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_857_419 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_857_419) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_857_419)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_857_419
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨857⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨857⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide +kernel) (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(720,427,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_720_427 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_720_427 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (720 : Fin 865)
      exact leaf_4_44_720
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (427 : Fin 865)
      exact leaf_4_44_427
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_720_427 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_720_427) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_720_427)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_720_427
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨720⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨720⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide +kernel) (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(860,427,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_860_427 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_860_427 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (860 : Fin 865)
      exact leaf_4_44_860
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (427 : Fin 865)
      exact leaf_4_44_427
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_860_427 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_860_427) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_860_427)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_860_427
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨860⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨860⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide +kernel) (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

end

end Work.BridgeSquare.SlabBuild
