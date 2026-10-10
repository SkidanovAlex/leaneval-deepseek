import Mathlib
import Submission.Work.LLink.Count

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LLink

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- The inverse of a pseudo-isomorphism is again a pseudo-isomorphism: `γ.symm` misses a
codimension-one point of its source only if that point is missing from `γ.target`, and
`IsPseudoIso.codim_target` rules that out. -/
theorem isPseudoIso_symm {X Y : Scheme.{0}} (γ : X.PartialIso Y) (hγ : γ.IsPseudoIso) :
    γ.symm.IsPseudoIso :=
  ⟨hγ.codim_target, hγ.codim_source⟩

end Work.LLink
