import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Main

/-- The "completed square" cubic `4X³ + b₂X² + 2b₄X + b₆` of a Weierstrass curve really is a cubic
in characteristic `≠ 2`. -/
theorem curveCubic_natDegree {F : Type*} [Field F] (E : WeierstrassCurve F) (h4 : (4 : F) ≠ 0) :
    (Work.Genus.curveCubic E).natDegree = 3 := by
  rw [show Work.Genus.curveCubic E =
      Polynomial.C (4 : F) * Polynomial.X ^ 3 + Polynomial.C E.b₂ * Polynomial.X ^ 2 +
        Polynomial.C (2 * E.b₄) * Polynomial.X + Polynomial.C E.b₆ from by
    simp only [Work.Genus.curveCubic, Polynomial.C_ofNat]]
  exact Polynomial.natDegree_cubic h4

end Work.Genus.Main
