import Mathlib
import Submission.Work.Whitney.RankTwo.RepDefs
import Submission.Work.Whitney.RankTwo.RepRelCoh
import Submission.Work.Whitney.RankTwo.RepEta
import Submission.Work.Whitney.RankTwo.RepCrux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Whitney.RankTwo

open Work.Thom Work.Cohomology Work.Thom.Orientation
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-- The pullback of cochains along a composite of continuous maps. -/
theorem pullCM_comp {A B Cc : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Cc]
    (f : C(A, B)) (g : C(B, Cc)) {n : ℕ} (α : Cochain ℤ (TopCat.toSSet.obj (TopCat.of Cc)) n) :
    pullCM f (pullCM g α) = pullCM (g.comp f) α := by
  apply genEval_ext
  intro σ
  rw [genEval_pullCM, genEval_pullCM, genEval_pullCM]
  congr 1

/-- `homeoSymm` is a left inverse of `capHomeo`: their composite is the cap map. -/
theorem homeoSymm_comp_capHomeo :
    (homeoSymm Y).comp (capHomeo Y) = capMapPairSph Y 1 := by
  apply ContinuousMap.ext
  intro q
  exact ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin 2)) (mSph 2))).symm_apply_apply
    (capMapPairSph Y 1 q)

/-- The pullback along the cap map is the pullback along `capHomeo` and then `homeoSymm`. -/
theorem pullCM_capHomeo_eq {n : ℕ} (ψ : Cochain ℤ (ssMSph2 Y) n) :
    pullCM (capHomeo Y) (pullCM (homeoSymm Y) ψ) = pullCM (capMapPairSph Y 1) ψ := by
  rw [pullCM_comp, homeoSymm_comp_capHomeo]

end

end Work.Whitney.RankTwo
