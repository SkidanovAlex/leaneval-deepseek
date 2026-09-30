/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The addition map of symmetric powers (area SY)

`Work.SymQuot.addMap C m n : Sym^m C ⊗ Sym^n C ⟶ Sym^{m+n} C` is the addition of symmetric
powers, characterised by

`lift (powMap x) (powMap y) ≫ addMap C m n = powMap (Fin.append x y)`

for all test schemes `T` and all `x : Fin m → (T ⟶ C)`, `y : Fin n → (T ⟶ C)`.  It is the
`GroupChunk.Input.addMap` field (the lead's `Submission/Work/NOTES_LEAD_jacobian_final.md` §2.2,
Step 2), built here from the relative quotient property
`Work.SymQuot.RelQuot.relQuot` via `RelQuot.exists_addMap`.
-/
import Submission.Work.SymQuot.RelQuot.exists_addMap
import Submission.Work.SymQuot.Sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonoidalCategory

universe u

namespace Work.SymQuot

/-- **Addition of symmetric powers**: the morphism `Sym^m C ⊗ Sym^n C ⟶ Sym^{m+n} C` whose
value on `(∑ x_i, ∑ y_j)` is `∑ (x_i ++ y_j)`. -/
noncomputable def addMap {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] (m n : ℕ) :
    Sym C m ⊗ Sym C n ⟶ Sym C (m + n) :=
  Classical.choose (RelQuot.exists_addMap C m n)

/-- The defining property of `addMap`. -/
theorem addMap_spec {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [CurveAffineCover C] (m n : ℕ) {T : Work.SpecLin.Sch K}
    (x : Fin m → (T ⟶ C.toOver)) (y : Fin n → (T ⟶ C.toOver)) :
    CartesianMonoidalCategory.lift (Sym.powMap C m x) (Sym.powMap C n y) ≫ addMap C m n
      = Sym.powMap C (m + n) (Fin.append x y) :=
  Classical.choose_spec (RelQuot.exists_addMap (C := C) m n) x y

end Work.SymQuot
