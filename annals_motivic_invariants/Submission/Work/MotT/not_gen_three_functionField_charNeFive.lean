import Submission.Work.MotT.not_gen_three_of_place
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

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Node R4-T: The T-twist route for `theorem_1_2_1 (b), (c), (d)` in characteristic `≠ 5`

For the function field `K = X.functionField` of a positive-dimensional `𝔽`-variety, with `𝔽` a
number field, finite, or algebraically closed, the T-route applies in every characteristic `≠ 5`:

* `𝔽` is perfect, so `K/𝔽` is separably generated; a separating transcendental `t` exists because
  `X` is positive-dimensional (`Work.MotR.Transcendental.exists_transcendental_of_pos_topologicalKrullDim`),
  hence `K` is infinite (node T12a, `Work.MotT.infinite_of_transcendental`);
* `K` is an essentially finite type extension of the perfect `𝔽`, so it has a place over the
  constants (`Work.MotR.FunctionField.hasFunctionFieldPlace_of_perfect_essFiniteType`, axiom-clean);
* T11 (`Work.MotT.not_gen_three_of_place`) then concludes.

This is the replacement of the (dead) S-route `KummerDescent` stack at the place: no `ζ₅`, no
cyclic extension, no ramification and no reduction theory is needed, the twist parameter is the
uniformizer `π` itself.

The conclusion is stated with the one remaining external input as an explicit hypothesis:

* `hlink : Work.MotT.LinkCertTInput K` — audit node T8 (the K-route link certificate census).

Everything else is discharged: node T7 (`Work.MotT.exists_kleinData_val`, the parametric Klein
model with unit parameters), node C2 (`Work.MotC2.aut_functionField` through
`Work.MotT.autRigidInput`), node T5, node T6 and node T9.
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- **R4-T.**  `theorem_1_2_1 (b), (c), (d)` in characteristic `≠ 5`: nodes T13a/T12a, T11a, T7,
C2, T5, T6 and T9 are discharged, so the only remaining input is the K-route census
`Work.MotT.LinkCertTInput` (node T8). -/
theorem not_gen_three_functionField_charNeFive (𝔽 : Type) [Field 𝔽]
    (X : AlgebraicGeometry.Scheme) [MotivicInvariants.Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : NumberField 𝔽 ∨ Finite 𝔽 ∨ IsAlgClosed 𝔽) (h5 : ringChar X.functionField ≠ 5)
    (hlink : LinkCertTInput X.functionField) :
    ¬ MotivicInvariants.GenByPseudoRegularizable X.functionField 3 := by
  letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
  -- (the `MotR` file holding `perfectField_of_cases` is temporarily unbuildable, so the three
  -- field classes are discharged inline; the argument is the same one)
  haveI : PerfectField 𝔽 := by
    rcases h with h | h | h
    · haveI : CharZero 𝔽 := h.to_charZero
      exact PerfectField.ofCharZero
    · exact PerfectField.ofFinite
    · exact h.perfectField
  haveI : Algebra.EssFiniteType 𝔽 X.functionField :=
    Work.MotR.FunctionField.essFiniteType_functionField 𝔽 X
  have ht := Work.MotR.Transcendental.exists_transcendental_of_pos_topologicalKrullDim 𝔽 X hX
  haveI : Infinite X.functionField := infinite_of_transcendental (𝔽 := 𝔽) ht
  obtain ⟨P⟩ := Work.MotR.FunctionField.hasFunctionFieldPlace_of_perfect_essFiniteType
    (𝔽 := 𝔽) (K := X.functionField) ht
  exact not_gen_three_of_place h5 hlink P

end

end Work.MotT
