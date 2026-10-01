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

/-- The chart identity of the flag `(629,438,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_629_438 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_629_438 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (629 : Fin 865)
      exact leaf_4_18_629
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (438 : Fin 865)
      exact leaf_4_18_438
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_629_438 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_629_438) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_629_438)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_629_438
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨629⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨629⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide +kernel) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(635,438,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_635_438 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_635_438 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (635 : Fin 865)
      exact leaf_4_18_635
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (438 : Fin 865)
      exact leaf_4_18_438
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_635_438 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_635_438) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_635_438)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_635_438
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨635⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨635⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide +kernel) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
