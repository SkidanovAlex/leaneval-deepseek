import Mathlib
import Submission.Work.K3.BaseChange

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.flat_baseChangeProj`

The projection `baseChangeProj K L X : X ×_{Spec K} Spec L ⟶ X` of the base change of a
`K`-scheme along a field extension `K → L` is flat, because it is the base change of the flat
structure morphism `specMap K L : Spec L ⟶ Spec K` and flatness is stable under base change.

-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.K3

/-- The structure morphism `Spec L ⟶ Spec K` of a field extension is flat: a field is flat as a
module over any subfield. -/
theorem flat_specMap (K L : Type) [Field K] [Field L] [Algebra K L] :
    AlgebraicGeometry.Flat (specMap K L) := by
  rw [specMap, AlgebraicGeometry.Flat.SpecMap_iff]
  exact RingHom.Flat.of_isField (Field.toIsField K) (algebraMap K L)

/-- **The projection of a base change along a field extension is flat.**  `baseChangeProj K L X`
is the base change of the flat morphism `specMap K L` along `X ⟶ Spec K`, and flatness is stable
under base change. -/
theorem flat_baseChangeProj (K L : Type) [Field K] [Field L] [Algebra K L]
    (X : AlgebraicGeometry.Scheme.{0}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] :
    AlgebraicGeometry.Flat (Work.K3.baseChangeProj K L X) := by
  haveI : AlgebraicGeometry.Flat (specMap K L) := flat_specMap K L
  show AlgebraicGeometry.Flat (CategoryTheory.Limits.pullback.snd (specMap K L)
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
  infer_instance

end Work.K3
