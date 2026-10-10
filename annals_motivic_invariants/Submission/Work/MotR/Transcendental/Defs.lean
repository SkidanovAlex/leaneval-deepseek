/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotR.Transcendental
-/
import Mathlib
import Submission.Work.FFResidual.Geometry.OverAlgebraDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The algebra structures of the sections of an `𝔽`-scheme

Node **R5** of the `Work.MotR` area (`exists_transcendental_of_pos_topologicalKrullDim`) needs the
constants to act on the *sections* `Γ(X, U)` of an open subscheme of an `𝔽`-scheme, compatibly with
the action on the function field `X.functionField = 𝒪_{X, η}` provided by
`Work.FFResidual.overFunctionFieldAlgebra`.

Everything here is the analogue of `Work.FFResidual.overStalkAlgebra` / `overFunctionFieldAlgebra`
for the section rings: the constants `𝔽` enter through the structure morphism
`𝔽 ≅ Γ(Spec 𝔽, ⊤) → Γ(X, ⊤) → Γ(X, U)`.

## Main definitions

* `Work.MotR.Transcendental.overSectionAlgebra` — `𝔽 → Γ(X, U)`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open AlgebraicGeometry CategoryTheory

namespace Work.MotR.Transcendental

noncomputable section

/-- **The constants act on the sections of an open subscheme** of an `𝔽`-scheme: the composite
`𝔽 → Γ(Spec 𝔽, ⊤) ≅ 𝔽 → Γ(X, ⊤) → Γ(X, U)`.

This is the section-ring analogue of `Work.FFResidual.overStalkAlgebra` and
`Work.FFResidual.overFunctionFieldAlgebra`, and is compatible with them (see
`Work.MotR.Transcendental.isScalarTower_overSectionAlgebra_overFunctionFieldAlgebra`). -/
@[instance_reducible]
noncomputable def overSectionAlgebra (𝔽 : Type) [Field 𝔽] (X : Scheme)
    [X.Over (Spec (CommRingCat.of 𝔽))] (U : X.Opens) : Algebra 𝔽 Γ(X, U) :=
  RingHom.toAlgebra (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of 𝔽)).inv ≫
    (X ↘ Spec (CommRingCat.of 𝔽)).appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op))

end

end Work.MotR.Transcendental
