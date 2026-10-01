import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts4_p1

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

/-- The chart identity of the flag `(734,374,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_734_374 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_734_374 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (734 : Fin 865)
      exact leaf_4_17_734
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (374 : Fin 865)
      exact leaf_4_17_374
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_734_374 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_734_374) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_734_374)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_734_374
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨734⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨734⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide +kernel) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(749,374,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_749_374 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_749_374 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (749 : Fin 865)
      exact leaf_4_17_749
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (374 : Fin 865)
      exact leaf_4_17_374
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_749_374 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_749_374) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_749_374)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_749_374
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨749⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨749⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide +kernel) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(588,471,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_588_471 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_588_471 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (588 : Fin 865)
      exact leaf_4_17_588
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (471 : Fin 865)
      exact leaf_4_17_471
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_588_471 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_588_471) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_588_471)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_588_471
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide +kernel) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(746,471,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_746_471 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_746_471 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (746 : Fin 865)
      exact leaf_4_17_746
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (471 : Fin 865)
      exact leaf_4_17_471
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_746_471 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_746_471) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_746_471)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_746_471
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨746⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨746⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide +kernel) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(588,479,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_588_479 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_588_479 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (588 : Fin 865)
      exact leaf_4_17_588
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (479 : Fin 865)
      exact leaf_4_17_479
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] fl_4_17_588_479 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_588_479) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_588_479)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_588_479
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide +kernel) (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w



end

end Work.BridgeSquare.SlabBuild
