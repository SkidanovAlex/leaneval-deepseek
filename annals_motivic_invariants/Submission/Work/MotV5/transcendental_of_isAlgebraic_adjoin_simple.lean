import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem transcendental_of_isAlgebraic_adjoin_simple {K A : Type*} [Field K] [Field A] [Algebra K A]
    {f x : A} (hx : Transcendental K x)
    (h : IsAlgebraic ↥(IntermediateField.adjoin K ({f} : Set A)) x) : Transcendental K f := by
  -- Contrapositive: if `f` were algebraic over `K`, then `K⟮f⟯` would be algebraic over `K`,
  -- hence `x` (algebraic over `K⟮f⟯`) would be algebraic over `K`, contradicting `hx`.
  intro hf
  have hL : Algebra.IsAlgebraic K ↥(IntermediateField.adjoin K ({f} : Set A)) :=
    IntermediateField.isAlgebraic_adjoin (S := ({f} : Set A))
      (fun y hy => (Set.mem_singleton_iff.mp hy) ▸ (isAlgebraic_iff_isIntegral.mp hf))
  exact hx ((Algebra.IsAlgebraic.isAlgebraic_iff (R := K)
    (S := ↥(IntermediateField.adjoin K ({f} : Set A)))).mpr h)

end Work.MotV5
