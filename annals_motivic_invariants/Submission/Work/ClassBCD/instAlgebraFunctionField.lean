/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.ClassBCD
-/
import Submission.Work.ClassBCD.nonempty_algebra_functionField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `𝔽`-algebra structure of the function field of an `𝔽`-scheme

The constant curve of the function-field classes is base changed along the structure map
`𝔽 → X.functionField`; the residual `Work.ClassBCD.FunctionFieldResidual 𝔽 X.functionField` is
stated with respect to such an `Algebra 𝔽 X.functionField`.  This file installs the instance, so
that the class theorems `Work.ClassBCD.hasPointlessTwist_functionField_*` can be applied without the
caller having to exhibit the structure map.

The underlying ring hom is the one of `Work.ClassBCD.nonempty_algebra_functionField` (built from
`X ↘ Spec 𝔽` through `ΓSpecIso` and the germ maps); only its *existence* is needed for the module's
results, and the instance is `noncomputable` for that reason.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open AlgebraicGeometry

namespace Work.ClassBCD

noncomputable section

/-- **The function field of an `𝔽`-scheme is an `𝔽`-algebra** (for `X.Over (Spec 𝔽)`).

Any `𝔽`-algebra structure on `X.functionField` does for the function-field classes; the instance is
provided so that the class theorems of `Work.ClassBCD` need only their residual as a hypothesis. -/
noncomputable instance instAlgebraFunctionField (𝔽 : Type) [Field 𝔽] (X : Scheme)
    [X.Over (Spec (CommRingCat.of 𝔽))] [IrreducibleSpace X] : Algebra 𝔽 X.functionField :=
  (nonempty_algebra_functionField 𝔽 X).some

end

end Work.ClassBCD
