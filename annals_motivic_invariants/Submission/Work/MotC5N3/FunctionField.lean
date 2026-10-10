import Mathlib
import ChallengeDeps
import Submission.Work.MotC5N3.Assembly
import Submission.Work.MotT.exists_val_of_place
import Submission.Work.MotT.infinite_of_transcendental
import Submission.Work.MotR.FunctionField.hasFunctionFieldPlace_of_perfect_essFiniteType
import Submission.Work.MotR.FunctionField.essFiniteType_functionField
import Submission.Work.MotR.Transcendental.exists_transcendental_of_pos_topologicalKrullDim

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Part N, function fields: `theorem_1_2_1 (c)`, `(d)` over a perfect base field

* `not_gen_three_of_place_charFive` — **N6**: the valuation-level result `N5` at a function-field
  place;
* `not_gen_three_functionField_charFive` — **N7**: `¬ GenByPseudoRegularizable X.functionField 3`
  for a positive-dimensional variety over a perfect field `𝔽` of characteristic `5`, the statement
  consumed by `theorem_1_2_1 (c)` (`𝔽` finite) and `(d)` (`𝔽` algebraically closed).
-/

set_option autoImplicit false

namespace Work.MotC5N3
noncomputable section

/-- **N6**: the `n = 3` characteristic-`5` result at a function-field place (char-5 analogue of
`Work.MotT.not_gen_three_of_place`). -/
theorem not_gen_three_of_place_charFive {𝔽 K : Type} [Field 𝔽] [Field K] [Algebra 𝔽 K]
    [Infinite K] (hk : ringChar K = 5) (P : Work.FFResidual.FunctionFieldPlace 𝔽 K) :
    ¬ MotivicInvariants.GenByPseudoRegularizable K 3 := by
  obtain ⟨v, hv⟩ := Work.MotT.exists_val_of_place P
  exact not_gen_three_of_val_charFive K hk v hv

/-- **N7**: function fields over a perfect field (in particular finite or algebraically closed),
characteristic `5`, `n = 3`: the statement consumed by `theorem_1_2_1 (c)`, `(d)`. -/
theorem not_gen_three_functionField_charFive (𝔽 : Type) [Field 𝔽] [PerfectField 𝔽]
    (X : AlgebraicGeometry.Scheme) [MotivicInvariants.Variety 𝔽 X]
    (hX : 0 < topologicalKrullDim X) (h5 : ringChar X.functionField = 5) :
    ¬ MotivicInvariants.GenByPseudoRegularizable X.functionField 3 := by
  letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
  haveI : Algebra.EssFiniteType 𝔽 X.functionField :=
    Work.MotR.FunctionField.essFiniteType_functionField 𝔽 X
  have ht := Work.MotR.Transcendental.exists_transcendental_of_pos_topologicalKrullDim 𝔽 X hX
  haveI : Infinite X.functionField := Work.MotT.infinite_of_transcendental (𝔽 := 𝔽) ht
  obtain ⟨P⟩ := Work.MotR.FunctionField.hasFunctionFieldPlace_of_perfect_essFiniteType
    (𝔽 := 𝔽) (K := X.functionField) ht
  exact not_gen_three_of_place_charFive h5 P

end
end Work.MotC5N3
