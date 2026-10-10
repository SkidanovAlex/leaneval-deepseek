import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.CY3Stab.Prod.excCount_eq_of_exDiv_image_twoBases

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

theorem cInv_prodMap_of_exDiv_image_twoBases (𝕜 : Type) [Field 𝕜] (k : ℕ)
    {X Y S S' : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 X]
    [MotivicInvariants.Variety 𝕜 Y] (φ : X.BirationalMap Y)
    [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    (p : X → Work.CY3Stab.WProd (𝕜 := 𝕜) X k) (q : Y → Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)
    (h : exDiv (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = p '' exDiv φ)
    (h' : exDiv ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm) = q '' exDiv φ.symm)
    (hp : Function.Injective p) (hq : Function.Injective q)
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [S'.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (z : S) (z' : S')
    (hr : ∀ x : X, ResEquiv 𝕜 (p x) z' ↔ ResEquiv 𝕜 x z)
    (hr' : ∀ y : Y, ResEquiv 𝕜 (q y) z' ↔ ResEquiv 𝕜 y z) :
    cInv 𝕜 z' (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = cInv 𝕜 z φ := by
  classical
  have h1 : excCount 𝕜 z' (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = excCount 𝕜 z φ :=
    excCount_eq_of_exDiv_image_twoBases 𝕜 z z' φ
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) p hp h hr
  have h2 : excCount 𝕜 z' ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm) =
      excCount 𝕜 z φ.symm :=
    excCount_eq_of_exDiv_image_twoBases 𝕜 z z' φ.symm
      ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm) q hq h' hr'
  unfold cInv
  rw [h2, h1]

end Work.CY3Stab.Prod
