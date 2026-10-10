/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotWire
-/
import Mathlib
import ChallengeDeps
import Submission.Work.MotWire.Defs
import Submission.Work.MotWire.linkCertTInput_of_charNeFive
import Submission.Work.MotWire.infinite_functionField
import Submission.Work.MotWire.MotV5Input
import Submission.Work.MotV.Final
import Submission.Work.MotT.not_gen_three_functionField_charNeFive

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# What the six holes really consume: `CharFiveMinimal`

`Submission/Work/MotWire/Wire.lean` proves the six holes of `Submission.lean` from the single input
`Work.MotWire.CharFiveInput`.  This module records that the three holes which split on
`ringChar = 5` consume strictly less, namely the two statements

* `Work.MotWire.CharFiveFunctionFieldInput` — the characteristic-`5`, `n = 3` case for the function
  field of a positive-dimensional variety (this is the paper's Theorem 1.2 (1) (c), (d) restricted to
  characteristic `5`, i.e. the `thm:ell-curves` construction of Lin–Shinder in characteristic `5`);
* `Work.MotWire.CharFiveInputN4` — the characteristic-`5` branch for `n ≥ 4`; by
  `Work.MotWire.charFiveInputN4_of_motV5` it is exactly the certificate hypothesis of the delivered
  `Work.MotV5.not_gen_charFive_all_of_linkCert`.

Their conjunction is `Work.MotWire.CharFiveMinimal`.  Moreover `CharFiveInput` implies
`CharFiveMinimal` (`charFiveMinimal_of_charFiveInput`), so the lead's suggested input remains the
one used by the wire; the point of the module is that a future discharge must produce only
`CharFiveFunctionFieldInput` and `MotV5LinkCertInput`, and nothing about `Cr₄` of an arbitrary
infinite field of characteristic `5`.

The three reduced statements (`theorem_1_2_1_c_of_minimal`, `…_d_of_minimal`,
`theorem_1_2_3_of_minimal`) have the same binders and conclusions as the corresponding holes, with
`CharFiveMinimal` in place of `CharFiveInput`.
-/

namespace Work.MotWire

open AlgebraicGeometry
open MotivicInvariants (GenByPseudoRegularizable Variety)

/-- **The `n = 3` half gives its function-field instances**: the passage from
`CharFiveInputThree` to `CharFiveFunctionFieldInput` only needs the infinitude of the function field
of a positive-dimensional variety (`Work.MotWire.infinite_functionField`). -/
theorem charFiveFunctionFieldInput_of_three (h : CharFiveInputThree) :
    CharFiveFunctionFieldInput :=
  fun 𝔽 _ X _ hX h5 => by
    haveI : Infinite ↥X.functionField := infinite_functionField 𝔽 X hX
    exact h ↥X.functionField h5

/-- **The general input implies the minimal one.**  Only the function-field instances of the `n = 3`
half are used, so `CharFiveInputThree` has to be restricted along the infinitude of the function
field (`Work.MotWire.infinite_functionField`). -/
theorem charFiveMinimal_of_charFiveInput (h : CharFiveInput) : CharFiveMinimal :=
  ⟨charFiveFunctionFieldInput_of_three (charFiveInput_three_of h), charFiveInput_n4_of h⟩

/-- **The minimal input from the two things that are actually missing.**  The `n ≥ 4` half is
discharged by the `MotV5` certificate hypothesis, so the only new content is
`Work.MotWire.CharFiveFunctionFieldInput`. -/
theorem charFiveMinimal_of_fnFieldInput_and_motV5 (h : CharFiveFunctionFieldInput)
    (hV5 : MotV5LinkCertInput) : CharFiveMinimal :=
  ⟨h, charFiveInputN4_of_motV5 hV5⟩

/-! ## The three characteristic-`5` holes, from the minimal input -/

/-- `theorem_1_2_1 (c)` from the minimal input: function fields over finite fields. -/
theorem theorem_1_2_1_c_of_minimal (hM : CharFiveMinimal) (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X) :
    ¬ GenByPseudoRegularizable X.functionField 3 := by
  haveI : Infinite ↥X.functionField := infinite_functionField 𝔽 X hX
  by_cases h5 : ringChar ↥X.functionField = 5
  · exact hM.1 𝔽 X hX h5
  · exact Work.MotT.not_gen_three_functionField_charNeFive 𝔽 X hX (Or.inr (Or.inl ‹Finite 𝔽›))
      h5 (linkCertTInput_of_charNeFive ↥X.functionField h5)

/-- `theorem_1_2_1 (d)` from the minimal input: function fields over algebraically closed fields. -/
theorem theorem_1_2_1_d_of_minimal (hM : CharFiveMinimal) (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X) :
    ¬ GenByPseudoRegularizable X.functionField 3 := by
  haveI : Infinite ↥X.functionField := infinite_functionField 𝔽 X hX
  by_cases h5 : ringChar ↥X.functionField = 5
  · exact hM.1 𝔽 X hX h5
  · exact Work.MotT.not_gen_three_functionField_charNeFive 𝔽 X hX (Or.inr (Or.inr ‹IsAlgClosed 𝔽›))
      h5 (linkCertTInput_of_charNeFive ↥X.functionField h5)

/-- `theorem_1_2_3` from the minimal input: only `n ≥ 5` is ever used in characteristic `5`, so the
`n ≥ 4` half of the input suffices. -/
theorem theorem_1_2_3_of_minimal (hM : CharFiveMinimal) (𝕜 : Type) [Field 𝕜] {n : ℕ} (hn : 5 ≤ n)
    [Infinite 𝕜] : ¬ GenByPseudoRegularizable 𝕜 n := by
  by_cases h5 : ringChar 𝕜 = 5
  · exact hM.2 𝕜 h5 (by omega)
  · exact Work.MotV.not_gen_charNeFive 𝕜 h5 (by omega)

end Work.MotWire
