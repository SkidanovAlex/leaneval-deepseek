import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.SlabBuild.Charts1_p1_p1
import Submission.Work.BridgeSquare.SlabBuild.Charts1_p1_p2

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

/-- The chart identity of the flag `(594,304,52)` of the square `5` of cusp `1`. -/
theorem ch_1_5_594_304 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 5 := by
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
      (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 5 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 5 (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_5_594_304 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (594 : Fin 865)
      exact leaf_1_5_594
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (304 : Fin 865)
      exact leaf_1_5_304
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (52 : Fin 865)
      exact leaf_1_5_52
  have hchart := cSimp_eq_chiRep 1 (a := 5) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_1_5_594_304 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_5_594_304) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (52 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_5_594_304)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨52⟩ : QbarCW.Cell) fl_1_5_594_304
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨594⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨594⟩ : QbarCell) < (⟨304⟩ : QbarCell) from by decide +kernel) (show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
