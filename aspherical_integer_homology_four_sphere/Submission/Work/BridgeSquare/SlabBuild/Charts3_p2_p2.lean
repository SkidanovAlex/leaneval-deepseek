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

/-- The chart identity of the flag `(822,516,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_822_516 :
    cChain 3 (slabV 3 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_822_516 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (822 : Fin 865)
      exact leaf_3_14_822
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (516 : Fin 865)
      exact leaf_3_14_516
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_3_14_822_516 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_822_516) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_822_516)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_822_516
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨822⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨822⟩ : QbarCell) < (⟨516⟩ : QbarCell) from by decide +kernel) (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_822_516) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(852,516,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_852_516 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_852_516 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (852 : Fin 865)
      exact leaf_3_14_852
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (516 : Fin 865)
      exact leaf_3_14_516
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_3_14_852_516 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_852_516) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_852_516)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_852_516
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨852⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨852⟩ : QbarCell) < (⟨516⟩ : QbarCell) from by decide +kernel) (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_852_516) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(681,532,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_681_532 :
    cChain 3 (slabV 3 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_681_532 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (681 : Fin 865)
      exact leaf_3_14_681
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (532 : Fin 865)
      exact leaf_3_14_532
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_3_14_681_532 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_681_532) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_681_532)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_681_532
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨681⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨681⟩ : QbarCell) < (⟨532⟩ : QbarCell) from by decide +kernel) (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_681_532) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(717,532,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_717_532 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_717_532 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (717 : Fin 865)
      exact leaf_3_14_717
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (532 : Fin 865)
      exact leaf_3_14_532
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_3_14_717_532 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_717_532) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_717_532)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_717_532
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨717⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨717⟩ : QbarCell) < (⟨532⟩ : QbarCell) from by decide +kernel) (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_532) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(717,564,157)` of the square `14` of cusp `3`. -/
theorem ch_3_14_717_564 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 14 := by
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
      (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 14 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 14 (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_14_717_564 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (717 : Fin 865)
      exact leaf_3_14_717
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (564 : Fin 865)
      exact leaf_3_14_564
    · show Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (157 : Fin 865)
      exact leaf_3_14_157
  have hchart := cSimp_eq_chiRep 3 (a := 14) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_3_14_717_564 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_14_717_564) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (157 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_14_717_564)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨157⟩ : QbarCW.Cell) fl_3_14_717_564
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨717⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨717⟩ : QbarCell) < (⟨564⟩ : QbarCell) from by decide +kernel) (show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨171, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (157 : Fin 865)) fl_3_14_717_564) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
