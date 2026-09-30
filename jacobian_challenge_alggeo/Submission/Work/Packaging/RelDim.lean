/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area P (packaging)
-/
import Mathlib
import Submission.Work.Packaging.Basic
import Submission.Work.Packaging.RelDim.exists_smoothOfRelativeDimension

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false



/-!
# Area P: the genus as the relative dimension of the Jacobian

The genus of a smooth proper curve is *read off* its Jacobian: the package gives a smooth group
scheme `J` over the field `k` with connected underlying space, and such a morphism is smooth of a
unique relative dimension. We take that number as the genus.

`Work.Packaging.RelDim.exists_smoothOfRelativeDimension` (existence of the relative dimension, from
the local constancy of the rank of the Kähler differentials) is what makes this well defined;
`RelDimUniq.genusOf_eq` shows that the result does not depend on the choice: any relative dimension
of `J` equals `genusOf Pkg` (using `Work.Packaging.RelDim.smoothOfRelativeDimension_unique`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped MonObj

namespace Work.Packaging.RelDim

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  {P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C}

/-- The relative dimension of the (smooth, connected) group scheme `J` of a Jacobian package: the
genus of the curve, read off `J`. -/
noncomputable def genusOf (Pkg : JacPkg C P0) : ℕ :=
  Classical.choose (exists_smoothOfRelativeDimension Pkg.J.hom)

/-- `J` is smooth of relative dimension `genusOf Pkg` over `Spec k`. -/
theorem smoothOfRelativeDimension_genusOf (Pkg : JacPkg C P0) :
    SmoothOfRelativeDimension (genusOf Pkg) Pkg.J.hom :=
  Classical.choose_spec (exists_smoothOfRelativeDimension Pkg.J.hom)

end Work.Packaging.RelDim
