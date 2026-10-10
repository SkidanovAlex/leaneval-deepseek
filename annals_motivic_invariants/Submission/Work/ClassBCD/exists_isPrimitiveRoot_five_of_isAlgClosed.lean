import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ClassBCD

/-- An algebraically closed field of characteristic different from `5` contains a primitive
5-th root of unity: it is separably closed, hence has enough roots of unity. -/
theorem exists_isPrimitiveRoot_five_of_isAlgClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (h5 : (5 : 𝔽) ≠ 0) : ∃ ζ : 𝔽, IsPrimitiveRoot ζ 5 :=
  (@IsSepClosed.hasEnoughRootsOfUnity 𝔽 _ 5 ⟨h5⟩ _).prim

end Work.ClassBCD
