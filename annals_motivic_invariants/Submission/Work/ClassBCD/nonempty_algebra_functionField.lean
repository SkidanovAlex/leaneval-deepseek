import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ClassBCD

open CategoryTheory

open AlgebraicGeometry in
/-- The function field of an irreducible scheme `X` over `Spec 𝔽` carries a
canonical `𝔽`-algebra structure.

The structure morphism `X ⟶ Spec 𝔽` induces on global sections a ring map
`𝔽 ≃ Γ(Spec 𝔽, ⊤) ⟶ Γ(X, ⊤)`, which composes with the canonical map
`Γ(X, ⊤) ⟶ X.functionField` into the stalk at the generic point (the function
field). Bundling this ring homomorphism via `RingHom.toAlgebra` gives the
required algebra structure. -/
theorem nonempty_algebra_functionField (𝔽 : Type) [Field 𝔽] (X : Scheme)
    [X.Over (Spec (CommRingCat.of 𝔽))] [IrreducibleSpace X] :
    Nonempty (Algebra 𝔽 X.functionField) := by
  refine ⟨RingHom.toAlgebra ?_⟩
  exact CommRingCat.Hom.hom <|
    (Scheme.ΓSpecIso (CommRingCat.of 𝔽)).inv ≫
      (X ↘ Spec (CommRingCat.of 𝔽)).appTop ≫
        X.germToFunctionField ⊤ (h := ⟨⟨genericPoint X, trivial⟩⟩)

end Work.ClassBCD
