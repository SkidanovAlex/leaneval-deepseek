/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area BcDiv: the `K`-algebra structure on a field extension obtained by composing

For a tower of fields `K → L → F` there are two natural ways of viewing an `L`-algebra `F` as a
`K`-algebra: by restricting scalars along `algebraMap K L`.  This file records that structure
(`Algebra.compHom`) and its basic properties, so that the algebraic-geometry arguments of area
BcDiv can be carried out over a field `F` which is obtained from a finite extension of a field
`F` over `L` (see for instance `Work.BcDiv.divOf_ptsK`).

This is the same (trivial) construction as `Work.Charts.compAlgebra`; it is repeated here so that
area BcDiv does not have to import area `CH`.

## Main definitions

* `Work.BcDiv.compAlgebra` — the `K`-algebra structure on an `L`-algebra `F`.

## Main results

* `Work.BcDiv.isScalarTower_compAlgebra`, `Work.BcDiv.algebraMap_compAlgebra`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

namespace Work.BcDiv

/-- The `K`-algebra structure on an `L`-algebra `F`, obtained from the composite of the
structure maps `K → L → F`. -/
abbrev compAlgebra (K : Type u) [CommSemiring K] (L : Type u) [CommSemiring L] [Algebra K L]
    (F : Type u) [CommSemiring F] [Algebra L F] : Algebra K F :=
  Algebra.compHom F (algebraMap K L)

/-- The two structure maps of the tower agree: the `K`-algebra structure `compAlgebra` on `F`
is compatible with the given `L`-algebra structure. -/
theorem isScalarTower_compAlgebra (K : Type u) [CommSemiring K] (L : Type u) [CommSemiring L]
    [Algebra K L] (F : Type u) [CommSemiring F] [Algebra L F] :
    letI : Algebra K F := compAlgebra K L F
    IsScalarTower K L F := by
  letI : Algebra K F := compAlgebra K L F
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- **The composite `K`-algebra structure is compatible with the tower `K → F → F'`**: if the
`K`-algebra structure on `F'` is the composite of `K → L → F'` (e.g. `compAlgebra K L F'`), then
the `K`-structures on `F` and `F'` and the `F`-structure on `F'` form a scalar tower. -/
theorem isScalarTower_compAlgebra_tower {K : Type u} [Field K] {L : Type u} [Field L]
    {F : Type u} [Field F] {F' : Type u} [Field F'] [Algebra K L] [Algebra K F]
    [Algebra K F'] [Algebra L F] [Algebra L F'] [Algebra F F'] [IsScalarTower K L F]
    [IsScalarTower L F F'] [IsScalarTower K L F']
    (h : ∀ x : K, algebraMap K F' x = algebraMap L F' (algebraMap K L x)) :
    IsScalarTower K F F' := by
  refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
  rw [h x, IsScalarTower.algebraMap_apply K L F x]
  exact IsScalarTower.algebraMap_apply L F F' (algebraMap K L x)

end Work.BcDiv
