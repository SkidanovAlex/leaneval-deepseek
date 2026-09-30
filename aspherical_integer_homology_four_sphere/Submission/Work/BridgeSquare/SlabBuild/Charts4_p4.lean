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

/-- The chart identity of the flag `(629,446,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_629_446 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_629_446 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (629 : Fin 865)
      exact leaf_4_18_629
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (446 : Fin 865)
      exact leaf_4_18_446
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] fl_4_18_629_446 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_629_446) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_629_446)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_629_446
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨629⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨629⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide +kernel) (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(638,446,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_638_446 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_638_446 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (638 : Fin 865)
      exact leaf_4_18_638
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (446 : Fin 865)
      exact leaf_4_18_446
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] fl_4_18_638_446 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_638_446) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_638_446)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_638_446
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨638⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨638⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide +kernel) (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(662,238,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_662_238 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_662_238 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (662 : Fin 865)
      exact leaf_4_20_662
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (238 : Fin 865)
      exact leaf_4_20_238
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] fl_4_20_662_238 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_662_238) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_662_238)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_662_238
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨662⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨662⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide +kernel) (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(674,238,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_674_238 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_674_238 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (674 : Fin 865)
      exact leaf_4_20_674
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (238 : Fin 865)
      exact leaf_4_20_238
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] fl_4_20_674_238 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_674_238) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_674_238)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_674_238
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨674⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨674⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide +kernel) (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(662,394,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_662_394 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_662_394 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (662 : Fin 865)
      exact leaf_4_20_662
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (394 : Fin 865)
      exact leaf_4_20_394
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] fl_4_20_662_394 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_662_394) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_662_394)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_662_394
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨662⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨662⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide +kernel) (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(677,394,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_677_394 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_677_394 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (677 : Fin 865)
      exact leaf_4_20_677
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (394 : Fin 865)
      exact leaf_4_20_394
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] fl_4_20_677_394 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_677_394) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_677_394)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_677_394
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨677⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨677⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide +kernel) (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(668,454,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_668_454 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_668_454 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (668 : Fin 865)
      exact leaf_4_20_668
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (454 : Fin 865)
      exact leaf_4_20_454
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] fl_4_20_668_454 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_668_454) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_668_454)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_668_454
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨668⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨668⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide +kernel) (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(674,454,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_674_454 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_674_454 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (674 : Fin 865)
      exact leaf_4_20_674
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (454 : Fin 865)
      exact leaf_4_20_454
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] fl_4_20_674_454 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_674_454) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_674_454)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_674_454
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨674⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨674⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide +kernel) (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(668,462,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_668_462 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_668_462 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (668 : Fin 865)
      exact leaf_4_20_668
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (462 : Fin 865)
      exact leaf_4_20_462
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] fl_4_20_668_462 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_668_462) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_668_462)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_668_462
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨668⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨668⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide +kernel) (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(677,462,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_677_462 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_677_462 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (677 : Fin 865)
      exact leaf_4_20_677
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (462 : Fin 865)
      exact leaf_4_20_462
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] fl_4_20_677_462 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_677_462) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_677_462)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_677_462
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨677⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨677⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide +kernel) (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(579,303,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_579_303 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_579_303 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (579 : Fin 865)
      exact leaf_4_21_579
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (303 : Fin 865)
      exact leaf_4_21_303
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] fl_4_21_579_303 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_579_303) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_579_303)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_579_303
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨579⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨579⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide +kernel) (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(614,303,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_614_303 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_614_303 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (614 : Fin 865)
      exact leaf_4_21_614
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (303 : Fin 865)
      exact leaf_4_21_303
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] fl_4_21_614_303 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_614_303) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_614_303)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_614_303
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨614⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨614⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide +kernel) (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(579,399,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_579_399 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_579_399 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (579 : Fin 865)
      exact leaf_4_21_579
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (399 : Fin 865)
      exact leaf_4_21_399
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] fl_4_21_579_399 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_579_399) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_579_399)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_579_399
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨579⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨579⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide +kernel) (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(617,399,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_617_399 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_617_399 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (617 : Fin 865)
      exact leaf_4_21_617
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (399 : Fin 865)
      exact leaf_4_21_399
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] fl_4_21_617_399 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_617_399) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_617_399)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_617_399
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨617⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨617⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide +kernel) (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(608,466,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_608_466 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_608_466 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (608 : Fin 865)
      exact leaf_4_21_608
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (466 : Fin 865)
      exact leaf_4_21_466
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] fl_4_21_608_466 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_608_466) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_608_466)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_608_466
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨608⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨608⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide +kernel) (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(614,466,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_614_466 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_614_466 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (614 : Fin 865)
      exact leaf_4_21_614
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (466 : Fin 865)
      exact leaf_4_21_466
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] fl_4_21_614_466 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_614_466) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_614_466)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_614_466
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨614⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨614⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide +kernel) (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(608,474,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_608_474 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_608_474 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (608 : Fin 865)
      exact leaf_4_21_608
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (474 : Fin 865)
      exact leaf_4_21_474
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] fl_4_21_608_474 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_608_474) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_608_474)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_608_474
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨608⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨608⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide +kernel) (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(617,474,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_617_474 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_617_474 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (617 : Fin 865)
      exact leaf_4_21_617
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (474 : Fin 865)
      exact leaf_4_21_474
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] fl_4_21_617_474 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_617_474) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_617_474)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_617_474
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨617⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨617⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide +kernel) (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(773,266,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_773_266 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_773_266 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (773 : Fin 865)
      exact leaf_4_22_773
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (266 : Fin 865)
      exact leaf_4_22_266
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_773_266 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_773_266) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_773_266)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_773_266
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨773⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨773⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide +kernel) (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(782,266,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_782_266 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_782_266 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (782 : Fin 865)
      exact leaf_4_22_782
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (266 : Fin 865)
      exact leaf_4_22_266
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_782_266 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_782_266) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_782_266)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_782_266
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨782⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨782⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide +kernel) (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(773,326,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_773_326 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_773_326 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (773 : Fin 865)
      exact leaf_4_22_773
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (326 : Fin 865)
      exact leaf_4_22_326
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_773_326 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_773_326) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_773_326)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_773_326
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨773⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨773⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide +kernel) (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(785,326,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_785_326 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_785_326 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (785 : Fin 865)
      exact leaf_4_22_785
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (326 : Fin 865)
      exact leaf_4_22_326
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_785_326 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_785_326) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_785_326)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_785_326
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨785⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨785⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide +kernel) (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
