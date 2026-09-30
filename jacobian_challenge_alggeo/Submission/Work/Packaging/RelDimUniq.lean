/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area P (packaging)
-/
import Mathlib
import Submission.Work.Packaging.RelDim
import Submission.Work.Packaging.RelDim.smoothOfRelativeDimension_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Area P: uniqueness of the genus

`Work.Packaging.RelDim.genusOf` is defined by choosing the relative dimension of the Jacobian. This
file records that the result does not depend on the choice: any relative dimension of `J` equals
`genusOf Pkg`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped MonObj

namespace Work.Packaging.RelDim

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  {P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C}

/-- Any relative dimension of `J` is the genus: the genus is well defined. -/
theorem genusOf_eq (Pkg : JacPkg C P0) (n : ℕ) [SmoothOfRelativeDimension n Pkg.J.hom] :
    genusOf Pkg = n := by
  haveI := smoothOfRelativeDimension_genusOf Pkg
  exact smoothOfRelativeDimension_unique Pkg.J.hom _ _

end Work.Packaging.RelDim
