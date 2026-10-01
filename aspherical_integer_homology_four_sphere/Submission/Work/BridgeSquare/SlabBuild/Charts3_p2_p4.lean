import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts3_p1

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

/-- The chart identity of the flag `(621,504,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_621_504 :
    cChain 3 (slabV 3 ![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_621_504 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (621 : Fin 865)
      exact leaf_3_15_621
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (504 : Fin 865)
      exact leaf_3_15_504
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_621_504 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_621_504) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_621_504)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_621_504
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨621⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨621⟩ : QbarCell) < (⟨504⟩ : QbarCell) from by decide +kernel) (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_504) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(660,504,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_660_504 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_660_504 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (660 : Fin 865)
      exact leaf_3_15_660
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (504 : Fin 865)
      exact leaf_3_15_504
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_660_504 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_660_504) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_660_504)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_660_504
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨660⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨660⟩ : QbarCell) < (⟨504⟩ : QbarCell) from by decide +kernel) (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_504) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(660,556,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_660_556 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_660_556 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (660 : Fin 865)
      exact leaf_3_15_660
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (556 : Fin 865)
      exact leaf_3_15_556
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_660_556 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_660_556) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_660_556)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_660_556
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨660⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨660⟩ : QbarCell) < (⟨556⟩ : QbarCell) from by decide +kernel) (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_660_556) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(804,556,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_804_556 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_804_556 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (804 : Fin 865)
      exact leaf_3_15_804
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (556 : Fin 865)
      exact leaf_3_15_556
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_804_556 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_804_556) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_804_556)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_804_556
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨804⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨804⟩ : QbarCell) < (⟨556⟩ : QbarCell) from by decide +kernel) (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_804_556) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(621,560,150)` of the square `15` of cusp `3`. -/
theorem ch_3_15_621_560 :
    cChain 3 (slabV 3 ![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 15 := by
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
      (slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 15 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 15 (slabL 3 (![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_15_621_560 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (621 : Fin 865)
      exact leaf_3_15_621
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (560 : Fin 865)
      exact leaf_3_15_560
    · show Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (150 : Fin 865)
      exact leaf_3_15_150
  have hchart := cSimp_eq_chiRep 3 (a := 15) rfl
    ![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ] fl_3_15_621_560 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_15_621_560) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (150 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_15_621_560)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨150⟩ : QbarCW.Cell) fl_3_15_621_560
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨621⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨621⟩ : QbarCell) < (⟨560⟩ : QbarCell) from by decide +kernel) (show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨77, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (150 : Fin 865)) fl_3_15_621_560) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
