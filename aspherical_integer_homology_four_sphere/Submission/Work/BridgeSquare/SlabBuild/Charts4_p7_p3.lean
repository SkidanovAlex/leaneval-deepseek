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

/-- The chart identity of the flag `(774,327,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_774_327 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_774_327 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (774 : Fin 865)
      exact leaf_4_34_774
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (327 : Fin 865)
      exact leaf_4_34_327
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_774_327 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_774_327) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_774_327)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_774_327
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨774⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨774⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide +kernel) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(800,327,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_800_327 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_800_327 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (800 : Fin 865)
      exact leaf_4_34_800
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (327 : Fin 865)
      exact leaf_4_34_327
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_800_327 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_800_327) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_800_327)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_800_327
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨800⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨800⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide +kernel) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(648,435,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_648_435 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_648_435 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (648 : Fin 865)
      exact leaf_4_34_648
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (435 : Fin 865)
      exact leaf_4_34_435
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_648_435 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_648_435) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_648_435)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_648_435
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide +kernel) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(797,435,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_797_435 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_797_435 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (797 : Fin 865)
      exact leaf_4_34_797
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (435 : Fin 865)
      exact leaf_4_34_435
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_797_435 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_797_435) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_797_435)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_797_435
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨797⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨797⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide +kernel) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(648,443,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_648_443 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_648_443 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (648 : Fin 865)
      exact leaf_4_34_648
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (443 : Fin 865)
      exact leaf_4_34_443
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_648_443 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_648_443) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_648_443)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_648_443
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide +kernel) (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w



end

end Work.BridgeSquare.SlabBuild
