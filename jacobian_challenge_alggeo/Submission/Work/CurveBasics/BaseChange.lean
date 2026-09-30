/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change of a curve along a field extension

A base change of a smooth proper geometrically irreducible curve is again one, so
`C ↦ C_F` is a functor from curves over `k` to curves over `F`.  The divisors, the order of
vanishing and the Riemann-Roch spaces of `C_F` are those of `C` base changed, see
`Work.CurveBasics.BaseChange.*`.
-/
import Submission.Work.CurveBasics.BaseChangeScheme
import Submission.Work.CurveBasics.BaseChange.krullDim_le_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- Base change of a curve along a field extension `F/k`. -/
noncomputable def baseChange (C : Curve k) (F : Type u) [Field F] [Algebra k F] : Curve F where
  toOver := baseChangeOver C F
  smooth := baseChange_smoothOfRelativeDimension C F
  proper := baseChange_isProper C F
  geomIrred := baseChange_geometricallyIrreducible C F
  geomReduced := baseChange_geometricallyReduced C F
  krullDim_stalk_le_one := Work.CurveBasics.BaseChange.krullDim_le_one C F
  nontrivial := inferInstance

instance (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    IsIntegral (baseChangeLeft C F) :=
  inferInstanceAs (IsIntegral (baseChange C F).left)

instance (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    IrreducibleSpace (baseChangeLeft C F) :=
  inferInstanceAs (IrreducibleSpace (baseChange C F).left)

instance (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    Nonempty (baseChangeLeft C F) :=
  inferInstanceAs (Nonempty (baseChange C F).left)

instance (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    IsLocallyNoetherian (baseChangeLeft C F) :=
  inferInstanceAs (IsLocallyNoetherian (baseChange C F).left)

instance (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    GeometricallyReduced (baseChangeHom C F) :=
  inferInstanceAs (GeometricallyReduced (baseChange C F).hom)

instance (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    GeometricallyIrreducible (baseChangeHom C F) :=
  inferInstanceAs (GeometricallyIrreducible (baseChange C F).hom)

@[simp]
theorem baseChange_left (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    (baseChange C F).left = baseChangeLeft C F := rfl

@[simp]
theorem baseChange_hom (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    (baseChange C F).hom = baseChangeHom C F := rfl

end

end Curve

end Work.CurveBasics
