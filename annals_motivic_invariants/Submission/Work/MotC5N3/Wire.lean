import Mathlib
import ChallengeDeps
import Submission.Work.MotC5N3.FunctionField
import Submission.Work.MotWire.infinite_functionField
import Submission.Work.MotWire.linkCertTInput_of_charNeFive
import Submission.Work.MotT.not_gen_three_functionField_charNeFive
import Submission.Work.MotV.Final
import Submission.Work.MotV5.ASChart.FinalAS

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Part W: the re-wiring of `theorem_1_2_1 (c)`, `(d)` and `theorem_1_2_3`

The three characteristic-`5` holes of `Submission.lean` are proved here without any named input:

* `theorem_1_2_1_c` (`𝔽` finite) and `theorem_1_2_1_d` (`𝔽` algebraically closed): in
  characteristic `5` the statement is `Work.MotC5N3.not_gen_three_functionField_charFive` (**N7**,
  which rides on the Artin–Schreier twist of the Klein curve, **N5** + the nodes of
  `Submission/Work/MotC5N3/`); in characteristic `≠ 5` it is the Kummer route
  `Work.MotT.not_gen_three_functionField_charNeFive` with the already-proved input
  `Work.MotWire.linkCertTInput_of_charNeFive`;
* `theorem_1_2_3`: in characteristic `5` it is `Work.MotV5.not_gen_charFive` (whose input is the AS
  census over `RatFunc 𝕜`), in characteristic `≠ 5` it is `Work.MotV.not_gen_charNeFive`.

This retires the input `Work.MotWire.CharFiveInput` (`Work.MotRoot.CharFiveInput_holds`), which
asserted `¬ GenByPseudoRegularizable 𝕜 3` for *every* infinite field of characteristic `5`,
including `𝔽̄₅` — that is not a theorem of Lin–Shinder and is not used here.
-/

set_option autoImplicit false

namespace Work.MotC5N3
noncomputable section

open AlgebraicGeometry MotivicInvariants

/-- **W1**: Theorem 1.2 (1) (c), with the binder list of `Submission.lean`. -/
theorem theorem_1_2_1_c (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X) :
    ¬ GenByPseudoRegularizable X.functionField 3 := by
  haveI : Infinite ↥X.functionField := Work.MotWire.infinite_functionField 𝔽 X hX
  by_cases h5 : ringChar ↥X.functionField = 5
  · haveI : PerfectField 𝔽 := PerfectField.ofFinite
    exact not_gen_three_functionField_charFive 𝔽 X hX h5
  · exact Work.MotT.not_gen_three_functionField_charNeFive 𝔽 X hX (Or.inr (Or.inl ‹Finite 𝔽›))
      h5 (Work.MotWire.linkCertTInput_of_charNeFive ↥X.functionField h5)

/-- **W2**: Theorem 1.2 (1) (d), with the binder list of `Submission.lean`. -/
theorem theorem_1_2_1_d (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X) :
    ¬ GenByPseudoRegularizable X.functionField 3 := by
  haveI : Infinite ↥X.functionField := Work.MotWire.infinite_functionField 𝔽 X hX
  by_cases h5 : ringChar ↥X.functionField = 5
  · haveI : PerfectField 𝔽 := IsAlgClosed.perfectField 𝔽
    exact not_gen_three_functionField_charFive 𝔽 X hX h5
  · exact Work.MotT.not_gen_three_functionField_charNeFive 𝔽 X hX (Or.inr (Or.inr ‹IsAlgClosed 𝔽›))
      h5 (Work.MotWire.linkCertTInput_of_charNeFive ↥X.functionField h5)

/-- **W3**: Theorem 1.2 (3) with no named input: characteristic `5` from
`Work.MotV5.not_gen_charFive` (`n ≥ 4`), characteristic `≠ 5` from `Work.MotV.not_gen_charNeFive`.
The binder list is that of `Submission.lean`. -/
theorem theorem_1_2_3 (𝕜 : Type) [Field 𝕜] {n : ℕ} (hn : 5 ≤ n) [Infinite 𝕜] :
    ¬ GenByPseudoRegularizable 𝕜 n := by
  by_cases h5 : ringChar 𝕜 = 5
  · exact Work.MotV5.not_gen_charFive 𝕜 h5 (by omega)
  · exact Work.MotV.not_gen_charNeFive 𝕜 h5 (by omega)

end
end Work.MotC5N3
