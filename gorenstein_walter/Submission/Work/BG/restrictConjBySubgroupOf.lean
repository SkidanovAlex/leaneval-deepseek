import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory in
theorem restrictConjBySubgroupOf {X : Type} [Group X] {U W : Subgroup X} [U.Normal] [W.Normal]
    (h : U ≤ W) (g : X) (τ : ClassFunction ↥W ℂ) :
    ClassFunction.restrict (U.subgroupOf W) (ClassFunction.conjBy (G := X) (H := W) g τ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
          (ClassFunction.conjBy (G := X) (H := U) g
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
              (ClassFunction.restrict (U.subgroupOf W) τ))) := by
  ext u
  simp only [ClassFunction.restrict_apply, ClassFunction.conjBy_apply, ClassFunction.compHom_apply]
  congr 1

end Work.BG
