import Mathlib
import Submission.Work.CrauderKatz.isFractionRing_polynomial_ratFunc
import Submission.Work.MotV5.fracMvPoly_tower

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem fractionRing_mvPoly_three_ratFunc_fractionRing_two {𝕜 F : Type} [Field 𝕜] [Field F]
    [Algebra 𝕜 F] :
    Nonempty (FractionRing (MvPolynomial (Fin 3) F) ≃ₐ[𝕜]
      RatFunc (FractionRing (MvPolynomial (Fin 2) F))) := by
  obtain ⟨e⟩ := fracMvPoly_succ_ratFunc (F := F) 2
  exact ⟨e.restrictScalars 𝕜⟩

end Work.MotV5
