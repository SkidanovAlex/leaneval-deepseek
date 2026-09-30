/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The affine case of the Galois quotient statement

If `X` is an affine `k`-scheme then the projection `X_{k'} ⟶ X` is the categorical quotient of
`X_{k'}` by the action of `Gal k k'`.  This follows from the model case
(`Work.Descent.AffineModelAux.affineModel_isGaloisQuotient`), the invariance of the statement under
isomorphisms of `k`-schemes (`Work.Descent.isGaloisQuotient_of_iso`) and the fact that every affine
`k`-scheme is isomorphic to a model `Spec A` (`Work.Descent.exists_iso_Aff`).
-/
import Mathlib
import Submission.Work.Descent.Scheme
import Submission.Work.Descent.QuotientSetup
import Submission.Work.Descent.AffineModelAux
import Submission.Work.Descent.isGaloisQuotient_of_iso
import Submission.Work.Descent.exists_iso_Aff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Work.Descent

/-- The affine case: for an affine `k`-scheme `X`, the projection `X_{k'} ⟶ X` is the categorical
quotient of `X_{k'}` by the Galois action. -/
theorem isGaloisQuotient_of_isAffine {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (X : Sch k) [IsAffine X.left] :
    IsGaloisQuotient k k' X := by
  obtain ⟨A, i1, i2, ⟨e⟩⟩ := exists_iso_Aff X
  letI := i1
  letI := i2
  exact (isGaloisQuotient_of_iso e).mpr
    (AffineModelAux.affineModel_isGaloisQuotient (k := k) (k' := k') A)

end Work.Descent
