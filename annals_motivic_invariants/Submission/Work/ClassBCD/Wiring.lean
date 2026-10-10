/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.ClassBCD
-/
import Submission.Work.ClassBCD.Defs
import Submission.Work.ClassBCD.instAlgebraFunctionField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The three function-field classes (b), (c), (d) of Theorem 1.2 (1)

This file wires the residual `Work.ClassBCD.FunctionFieldResidual` of the function-field classes to
the arithmetic half `Work.PointlessTwist.HasPointlessTwist 𝕜` of the `Work.Twist` chain, for each of
the three field classes of Lin–Shinder, *Motivic invariants of birational maps*, Annals of Math.
**199** (1), 2024, Theorem 1.2 (1):

| class | `𝔽` | `𝕜` | `L/𝕜` | residual |
|---|---|---|---|---|
| (b) | number field | `X.functionField`, `0 < dim X` | Kummer `s ^ 5 = t` (or the cyclotomic/AS route) | `FunctionFieldResidual 𝔽 𝕜` |
| (c) | finite field | `X.functionField`, `0 < dim X` | Kummer `s ^ 5 = t` (`ζ₅ ∈ 𝔽` when `5 ∣ #𝔽 - 1`), AS in characteristic `5` | `FunctionFieldResidual 𝔽 𝕜` |
| (d) | algebraically closed | `X.functionField`, `0 < dim X` | Kummer (char `≠ 5`), AS (char `5`) | `FunctionFieldResidual 𝔽 𝕜` |

The three theorems below are the composition

  `FunctionFieldResidual 𝔽 𝕜 → PointlessOf C₅ L → HasPointlessTwist 𝕜`

at the concrete data, in the exact shape of the class statements: `𝕜` is the **function field of a
positive-dimensional `𝔽`-variety** `X`, so that the result feeds directly into
`Work.Twist.hasLLinkCurve_pointlessTwistDataAny_functionField_*` /
`Work.PointlessIndexFive.hasPointlessIndexFiveCurve_functionField_*`.

## Main results

* `hasPointlessTwist_functionField_numberField` — class (b).
* `hasPointlessTwist_functionField_finite` — class (c).
* `hasPointlessTwist_functionField_algClosed` — class (d).
* `hasPointlessTwist_ratFunc` — the same at `𝕜 = 𝔽(t)` (`RatFunc 𝔽`), the case which is *proved*
  unconditionally in `Work.ClassBCD.RatFunc`.

## Note on the `𝔽`-algebra structure of `X.functionField`

`FunctionFieldResidual 𝔽 X.functionField` is a statement about the function field as an `𝔽`-algebra:
the structure map is the one along which the *constant* curve is base changed.  It exists for any
`X.Over (Spec 𝔽)` (`Work.ClassBCD.nonempty_algebra_functionField`) and is installed as the instance
`Work.ClassBCD.instAlgebraFunctionField`, so that the class theorems below need only their residual
as a hypothesis.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open AlgebraicGeometry MotivicInvariants

namespace Work.ClassBCD

noncomputable section

/-- **The three function-field classes, uniformly.**  For a field `𝔽`, a field `𝕜` with an
`𝔽`-algebra structure, the residual `FunctionFieldResidual 𝔽 𝕜` gives the arithmetic half of the
chain, in the `DecidableEq`-free form used by the parent chapters. -/
theorem hasPointlessTwist_of_functionFieldResidual (𝔽 : Type) [Field 𝔽]
    (𝕜 : Type) [Field 𝕜] [Algebra 𝔽 𝕜] (h : FunctionFieldResidual 𝔽 𝕜) :
    ∃ dec : DecidableEq 𝕜, @Work.PointlessTwist.HasPointlessTwist 𝕜 _ dec :=
  h.exists_hasPointlessTwist

/-- **Class (b) of Theorem 1.2 (1): function fields over a number field.**  Here `𝕜 = X.functionField`
is the function field of a positive-dimensional `𝔽`-variety, `𝔽` a number field, and the residual
`FunctionFieldResidual 𝔽 𝕜` is the concrete constant Tate model over `𝔽`, a cyclic quintic
extension `L/𝕜` and the place obstruction at `L.L` (see `Work.ClassBCD`'s `NOTES.md` for its precise
content and for the two provable forms). -/
theorem hasPointlessTwist_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (X : Scheme) [Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    (h : FunctionFieldResidual 𝔽 X.functionField) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec :=
  h.exists_hasPointlessTwist

/-- **Class (c) of Theorem 1.2 (1): function fields over a finite field.** -/
theorem hasPointlessTwist_functionField_finite (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme) [Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    (h : FunctionFieldResidual 𝔽 X.functionField) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec :=
  h.exists_hasPointlessTwist

/-- **Class (d) of Theorem 1.2 (1): function fields over an algebraically closed field.** -/
theorem hasPointlessTwist_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme) [Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    (h : FunctionFieldResidual 𝔽 X.functionField) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec :=
  h.exists_hasPointlessTwist

/-- **The three classes at `𝕜 = 𝔽(t)`**: the residual at the rational function field gives the
arithmetic half (and, by `Work.ClassBCD.RatFunc`, is proved there). -/
theorem hasPointlessTwist_ratFunc (𝔽 : Type) [Field 𝔽]
    (h : FunctionFieldResidual 𝔽 (RatFunc 𝔽)) :
    ∃ dec : DecidableEq (RatFunc 𝔽),
      @Work.PointlessTwist.HasPointlessTwist (RatFunc 𝔽) _ dec :=
  h.exists_hasPointlessTwist

/-! ## The three classes from the *place* datum

`FunctionFieldPlaceDatum 𝔽 𝕜` is the honest form of the residual in which the paper's proof
produces the obstruction: a place of `L.L` at which the Silverman reduction map decides the class of
the twist.  It is *strictly stronger* than the residual `FunctionFieldResidual 𝔽 𝕜`
(`FunctionFieldPlaceDatum.toResidual`), and these three theorems are the class statements in that
form. -/

/-- **Class (b) from the place datum.** -/
theorem hasPointlessTwist_functionField_numberField_of_placeDatum (𝔽 : Type) [Field 𝔽]
    [NumberField 𝔽] (X : Scheme) [Variety 𝔽 X]
    (_hX : 0 < topologicalKrullDim X) (h : FunctionFieldPlaceDatum 𝔽 X.functionField) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec :=
  (FunctionFieldPlaceDatum.toResidual h).exists_hasPointlessTwist

/-- **Class (c) from the place datum.** -/
theorem hasPointlessTwist_functionField_finite_of_placeDatum (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme) [Variety 𝔽 X]
    (_hX : 0 < topologicalKrullDim X) (h : FunctionFieldPlaceDatum 𝔽 X.functionField) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec :=
  (FunctionFieldPlaceDatum.toResidual h).exists_hasPointlessTwist

/-- **Class (d) from the place datum.** -/
theorem hasPointlessTwist_functionField_algClosed_of_placeDatum (𝔽 : Type) [Field 𝔽]
    [IsAlgClosed 𝔽] (X : Scheme) [Variety 𝔽 X]
    (_hX : 0 < topologicalKrullDim X) (h : FunctionFieldPlaceDatum 𝔽 X.functionField) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec :=
  (FunctionFieldPlaceDatum.toResidual h).exists_hasPointlessTwist

/-- **The three classes from the `ConstantsOnly` datum** (the trivial-Galois-action form of the
obstruction).  This is the form in which the obstruction is *proved* at `𝕜 = 𝔽(t)`
(`Work.ClassBCD.RatFunc`); at a general function field `X.functionField` it is a genuine
restriction (a positive-dimensional `X` may map non-constantly to the constant curve). -/
theorem hasPointlessTwist_functionField_numberField_of_constantsOnly (𝔽 : Type) [Field 𝔽]
    [NumberField 𝔽] (X : Scheme) [Variety 𝔽 X]
    (_hX : 0 < topologicalKrullDim X) (h : FunctionFieldConstantsOnlyDatum 𝔽 X.functionField) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec :=
  (FunctionFieldConstantsOnlyDatum.toResidual h).exists_hasPointlessTwist

end

end Work.ClassBCD
