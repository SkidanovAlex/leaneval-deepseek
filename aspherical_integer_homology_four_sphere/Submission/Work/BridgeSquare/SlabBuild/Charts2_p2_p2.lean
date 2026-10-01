import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts2_p1

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

/-- The chart identity of the flag `(750,392,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_750_392 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_750_392 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (750 : Fin 865)
      exact leaf_2_10_750
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (392 : Fin 865)
      exact leaf_2_10_392
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_2_10_750_392 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_750_392) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_750_392)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_750_392
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨750⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨750⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide +kernel) (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(819,392,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_819_392 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_819_392 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (819 : Fin 865)
      exact leaf_2_10_819
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (392 : Fin 865)
      exact leaf_2_10_392
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_2_10_819_392 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_819_392) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_819_392)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_819_392
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨819⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨819⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide +kernel) (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(597,416,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_597_416 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_597_416 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (597 : Fin 865)
      exact leaf_2_10_597
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (416 : Fin 865)
      exact leaf_2_10_416
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_2_10_597_416 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_597_416) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_597_416)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_597_416
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨597⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨597⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide +kernel) (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(678,416,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_678_416 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_678_416 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (678 : Fin 865)
      exact leaf_2_10_678
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (416 : Fin 865)
      exact leaf_2_10_416
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_2_10_678_416 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_678_416) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_678_416)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_678_416
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨678⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨678⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide +kernel) (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(678,464,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_678_464 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_678_464 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (678 : Fin 865)
      exact leaf_2_10_678
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (464 : Fin 865)
      exact leaf_2_10_464
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_2_10_678_464 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_678_464) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_678_464)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_678_464
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨678⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨678⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide +kernel) (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
