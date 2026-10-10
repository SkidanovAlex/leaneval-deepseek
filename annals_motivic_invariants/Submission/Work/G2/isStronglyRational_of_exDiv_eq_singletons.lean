import Mathlib
import Submission.Work.G2.Defs
import Submission.Work.LLink.Count
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.G2

theorem isStronglyRational_of_exDiv_eq_singletons {𝕜 : Type} [Field 𝕜] {n : ℕ}
    {X : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 X]
    (φ : X.BirationalMap (Work.CY3.ProjectiveSpace 𝕜 n))
    [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    {x : X} {y : Work.CY3.ProjectiveSpace 𝕜 n}
    (hx : exDiv φ = {x}) (hy : exDiv φ.symm = {y}) (h : ResEquiv 𝕜 x y) :
    Work.CY3.IsStronglyRational 𝕜 X n := by
  refine ⟨φ, inferInstance, ?_⟩
  intro W hW w
  have hEq : excCount 𝕜 w φ.symm = excCount 𝕜 w φ := by
    by_cases hw : ResEquiv 𝕜 x w
    · rw [Work.LLink.excCount_eq_one_of_exDiv_eq_singleton
          (X := Work.CY3.ProjectiveSpace 𝕜 n) (Y := X) w φ.symm hy
          (Work.Motivic.ResEquiv.trans (Work.Motivic.ResEquiv.symm h) hw),
        Work.LLink.excCount_eq_one_of_exDiv_eq_singleton w φ hx hw]
    · rw [Work.LLink.excCount_eq_zero_of_exDiv_eq_singleton
          (X := Work.CY3.ProjectiveSpace 𝕜 n) (Y := X) w φ.symm hy
          (fun hyw => hw (Work.Motivic.ResEquiv.trans h hyw)),
        Work.LLink.excCount_eq_zero_of_exDiv_eq_singleton w φ hx hw]
  show cInv 𝕜 w φ = 0
  unfold cInv
  rw [hEq]
  first | refl_ring1 | ring

end Work.G2
