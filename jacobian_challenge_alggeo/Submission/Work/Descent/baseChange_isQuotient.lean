import Mathlib
import Submission.Work.Descent.Basic
import Submission.Work.Descent.Scheme
import Submission.Work.Descent.AffineCase
import Submission.Work.Descent.isGaloisQuotient_of_affineOpens

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Descent

universe u

open CategoryTheory Limits AlgebraicGeometry

/-- The projection `X_{k'} ⟶ X` is the categorical quotient of `X_{k'}` by the action of the
Galois group `Gal k k'`: every `Γ`-invariant morphism of `k`-schemes out of `X_{k'}` factors
uniquely through the projection. -/
theorem baseChange_isQuotient {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (X : Sch k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] :
    IsGaloisQuotient k k' X := by
  refine isGaloisQuotient_of_affineOpens X ?_
  intro U hU
  have hU' : IsAffine (Over.mk (U.ι ≫ X.hom)).left := hU
  exact isGaloisQuotient_of_isAffine (Over.mk (U.ι ≫ X.hom))

end Work.Descent
