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

/-- The chart identity of the flag `(687,459,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_687_459 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_687_459 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (687 : Fin 865)
      exact leaf_4_37_687
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (459 : Fin 865)
      exact leaf_4_37_459
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_687_459 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_687_459) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_687_459)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_687_459
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨687⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨687⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide +kernel) (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(833,459,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_833_459 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_833_459 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (833 : Fin 865)
      exact leaf_4_37_833
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (459 : Fin 865)
      exact leaf_4_37_459
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_833_459 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_833_459) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_833_459)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_833_459
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨833⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨833⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide +kernel) (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(702,235,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_702_235 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_702_235 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (702 : Fin 865)
      exact leaf_4_40_702
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (235 : Fin 865)
      exact leaf_4_40_235
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_702_235 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_702_235) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_702_235)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_702_235
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨702⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨702⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide +kernel) (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(725,235,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_725_235 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_725_235 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (725 : Fin 865)
      exact leaf_4_40_725
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (235 : Fin 865)
      exact leaf_4_40_235
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_725_235 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_725_235) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_725_235)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_725_235
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨725⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨725⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide +kernel) (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(702,347,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_702_347 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_702_347 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (702 : Fin 865)
      exact leaf_4_40_702
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (347 : Fin 865)
      exact leaf_4_40_347
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_702_347 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_702_347) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_702_347)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_702_347
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨702⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨702⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide +kernel) (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(728,347,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_728_347 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_728_347 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (728 : Fin 865)
      exact leaf_4_40_728
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (347 : Fin 865)
      exact leaf_4_40_347
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_728_347 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_728_347) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_728_347)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_728_347
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨728⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨728⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide +kernel) (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(719,418,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_719_418 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_719_418 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (719 : Fin 865)
      exact leaf_4_40_719
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (418 : Fin 865)
      exact leaf_4_40_418
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_719_418 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_719_418) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_719_418)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_719_418
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨719⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨719⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide +kernel) (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(725,418,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_725_418 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_725_418 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (725 : Fin 865)
      exact leaf_4_40_725
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (418 : Fin 865)
      exact leaf_4_40_418
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_725_418 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_725_418) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_725_418)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_725_418
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨725⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨725⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide +kernel) (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(719,426,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_719_426 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_719_426 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (719 : Fin 865)
      exact leaf_4_40_719
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (426 : Fin 865)
      exact leaf_4_40_426
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_719_426 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_719_426) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_719_426)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_719_426
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨719⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨719⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide +kernel) (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(728,426,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_728_426 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_728_426 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (728 : Fin 865)
      exact leaf_4_40_728
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (426 : Fin 865)
      exact leaf_4_40_426
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_728_426 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_728_426) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_728_426)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_728_426
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨728⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨728⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide +kernel) (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(840,203,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_840_203 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_840_203 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (840 : Fin 865)
      exact leaf_4_44_840
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (203 : Fin 865)
      exact leaf_4_44_203
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_840_203 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_840_203) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_840_203)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_840_203
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨840⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨840⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide +kernel) (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(857,203,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_857_203 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_857_203 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (857 : Fin 865)
      exact leaf_4_44_857
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (203 : Fin 865)
      exact leaf_4_44_203
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_857_203 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_857_203) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_857_203)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_857_203
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨857⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨857⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide +kernel) (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(840,323,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_840_323 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_840_323 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (840 : Fin 865)
      exact leaf_4_44_840
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (323 : Fin 865)
      exact leaf_4_44_323
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_840_323 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_840_323) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_840_323)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_840_323
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨840⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨840⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide +kernel) (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(860,323,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_860_323 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_860_323 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (860 : Fin 865)
      exact leaf_4_44_860
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (323 : Fin 865)
      exact leaf_4_44_323
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_860_323 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_860_323) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_860_323)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_860_323
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨860⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨860⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide +kernel) (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(720,419,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_720_419 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_720_419 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (720 : Fin 865)
      exact leaf_4_44_720
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (419 : Fin 865)
      exact leaf_4_44_419
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_720_419 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_720_419) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_720_419)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_720_419
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨720⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨720⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide +kernel) (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

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
