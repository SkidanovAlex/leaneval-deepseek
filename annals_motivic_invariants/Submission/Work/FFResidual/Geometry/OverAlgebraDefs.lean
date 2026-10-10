/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Mathlib
import Submission.Work.FFResidual.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The algebra structure of the stalks of an `𝔽`-scheme

For `X` a scheme over `Spec 𝔽` and `z : X`, the structure morphism `X ↘ Spec 𝔽` maps the constants
into every local ring and into the function field, compatibly:

  `𝔽 → Γ(X, ⊤) → 𝒪_{X,z} → X.functionField`.

This file exhibits the algebra structures `overStalkAlgebra 𝔽 X z : Algebra 𝔽 (𝒪_{X,z})` and
`overFunctionFieldAlgebra 𝔽 X : Algebra 𝔽 X.functionField` *explicitly* (rather than through the
opaque `Nonempty` of `Work.ClassBCD.nonempty_algebra_functionField`), together with the scalar tower
`IsScalarTower 𝔽 𝒪_{X,z} X.functionField`.  The place of a function field over its constants, and
hence the function-field residual of `Work.FFResidual`, is stated with respect to these structures.

## Main results

* `Work.FFResidual.overStalkAlgebra` — `𝔽 → 𝒪_{X,z}`.
* `Work.FFResidual.overFunctionFieldAlgebra` — `𝔽 → X.functionField`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open AlgebraicGeometry CategoryTheory

namespace Work.FFResidual

noncomputable section

/-- **The constants act on the local ring** `𝒪_{X,z}` of a point of an `𝔽`-scheme: the composite
`𝔽 → Γ(Spec 𝔽, ⊤) ≅ 𝔽 → Γ(X, ⊤) → 𝒪_{X,z}`. -/
@[instance_reducible]
noncomputable def overStalkAlgebra (𝔽 : Type) [Field 𝔽] (X : Scheme)
    [X.Over (Spec (CommRingCat.of 𝔽))] (z : X) : Algebra 𝔽 (X.presheaf.stalk z) :=
  RingHom.toAlgebra (CommRingCat.Hom.hom
    ((Scheme.ΓSpecIso (CommRingCat.of 𝔽)).inv ≫
      (X ↘ Spec (CommRingCat.of 𝔽)).appTop ≫ X.presheaf.germ ⊤ z trivial))

/-- **The constants act on the function field** of an irreducible `𝔽`-scheme: the composite
`𝔽 → Γ(X, ⊤) → X.functionField`. -/
@[instance_reducible]
noncomputable def overFunctionFieldAlgebra (𝔽 : Type) [Field 𝔽] (X : Scheme)
    [X.Over (Spec (CommRingCat.of 𝔽))] [IrreducibleSpace X] : Algebra 𝔽 X.functionField :=
  RingHom.toAlgebra (CommRingCat.Hom.hom
    ((Scheme.ΓSpecIso (CommRingCat.of 𝔽)).inv ≫
      (X ↘ Spec (CommRingCat.of 𝔽)).appTop ≫
        X.germToFunctionField ⊤ (h := ⟨⟨genericPoint X, trivial⟩⟩)))

end

end Work.FFResidual
