import Mathlib
import Submission.Work.G2.Defs
import Submission.Work.LLink.Count

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.G2

theorem stronglyBirational_of_exDiv_eq_singletons {𝕜 : Type} [Field 𝕜] {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y]
    (φ : X.BirationalMap Y) [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    {x : X} {y : Y} (hx : exDiv φ = {x}) (hy : exDiv φ.symm = {y}) (h : ResEquiv 𝕜 x y) :
    Work.CY3.StronglyBirational 𝕜 X Y := by
  classical
  refine ⟨φ, inferInstance, ?_⟩
  intro Z hZ z
  unfold cInv
  by_cases hxz : ResEquiv 𝕜 x z
  · have hyz : ResEquiv 𝕜 y z := Work.Motivic.ResEquiv.trans (Work.Motivic.ResEquiv.symm h) hxz
    have h1 : excCount 𝕜 z φ.symm = 1 :=
      Work.LLink.excCount_eq_one_of_exDiv_eq_singleton (X := Y) (Y := X) z φ.symm hy hyz
    have h2 : excCount 𝕜 z φ = 1 :=
      Work.LLink.excCount_eq_one_of_exDiv_eq_singleton z φ hx hxz
    rw [h1, h2]
    norm_num
  · have hyz : ¬ ResEquiv 𝕜 y z := fun hyz => hxz (Work.Motivic.ResEquiv.trans h hyz)
    have h1 : excCount 𝕜 z φ.symm = 0 :=
      Work.LLink.excCount_eq_zero_of_exDiv_eq_singleton (X := Y) (Y := X) z φ.symm hy hyz
    have h2 : excCount 𝕜 z φ = 0 :=
      Work.LLink.excCount_eq_zero_of_exDiv_eq_singleton z φ hx hxz
    rw [h1, h2]
    norm_num

end Work.G2
