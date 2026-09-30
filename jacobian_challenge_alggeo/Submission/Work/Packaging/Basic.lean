/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area P (packaging)
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Area P: the Jacobian package

This file defines `Work.Packaging.JacPkg`, the interface through which the construction of the
Jacobian of a smooth proper geometrically irreducible curve (areas GC/UP of the blueprint) feeds
the definitions in `Submission.lean`.

`JacPkg C P0` carries

* a group scheme `J` over `Spec k`, proper, geometrically irreducible, smooth over `k`, with
  connected underlying space, together with
* the Abel–Jacobi map `AJ₀ : C ⟶ J` based at the `k`-point `P0` of `C` (so `P0 ≫ AJ₀ = η`),
* the universal property `univ₀` of `AJ₀` for maps out of `C` sending `P0` to `η`, and
* the "separation" statement `epi₀`: `AJ₀` is an epimorphism in the category of abelian
  varieties, i.e. two morphisms out of `J` agreeing on (the image of) `C` are equal.

`epi₀` is *not* an extra mathematical assumption: together with `univ₀` it is equivalent to the
full universal property of the Jacobian for *all* base points (`Work.Packaging.exists_unique_ofCurve_comp`
below). It is a separate field because it is not derivable from `univ₀` alone (it is the statement
that `AJ₀(C)` generates `J`).

The only *mathematical* input of the downstream files of area P is a proof of
`∀ P0, Nonempty (JacPkg C P0)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped MonObj

namespace Work.Packaging

/-- A "Jacobian package" for a curve `C : Over (Spec k)` with a `k`-point `P0`.

It bundles a group scheme `J` (the Jacobian), the Abel–Jacobi map `AJ₀` based at `P0` and the
universal property of `AJ₀`.

The typeclass fields on `J` are exactly the properties required by the challenge statement:
`GrpObj`, `IsProper`, `GeometricallyIrreducible`, `Smooth`, `ConnectedSpace J.left`.  The last one is
what turns `Smooth` into `SmoothOfRelativeDimension (genus C)`: the genus is *read off* `J` as its
relative dimension (`Work.Packaging.RelDim.genusOf`, using
`Work.Packaging.RelDim.exists_smoothOfRelativeDimension`), so the package does not have to carry the
dimension. -/
structure JacPkg {k : Type u} [Field k] (C : Over (Spec (.of k)))
    (P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C) where
  /-- The Jacobian of `C`. -/
  J : Over (Spec (.of k))
  [instGrpObj : GrpObj J]
  [instIsProper : IsProper J.hom]
  [instGeomIrred : GeometricallyIrreducible J.hom]
  [instSmooth : Smooth J.hom]
  [instConnected : ConnectedSpace J.left]
  /-- The Abel–Jacobi map based at `P0`. -/
  AJ₀ : C ⟶ J
  /-- `AJ₀` sends `P0` to the origin. -/
  AJ₀_pt : P0 ≫ AJ₀ = η[J]
  /-- The universal property of `AJ₀` for maps sending `P0` to `η`. -/
  univ₀ : ∀ (A : Over (Spec (.of k))) [Smooth A.hom] [IsProper A.hom]
    [GeometricallyIrreducible A.hom] [GrpObj A] (f : C ⟶ A),
    P0 ≫ f = η[A] → ∃! g : J ⟶ A, f = AJ₀ ≫ g
  /-- `AJ₀` is an epimorphism onto abelian varieties: a morphism out of `J` agreeing with another
  one on `C` is equal to it. (Equivalently: the image of `AJ₀` generates `J`.) -/
  epi₀ : ∀ (A : Over (Spec (.of k))) [Smooth A.hom] [IsProper A.hom]
    [GeometricallyIrreducible A.hom] [GrpObj A] (u v : J ⟶ A), AJ₀ ≫ u = AJ₀ ≫ v → u = v

attribute [instance] JacPkg.instGrpObj JacPkg.instIsProper JacPkg.instGeomIrred JacPkg.instSmooth
  JacPkg.instConnected

end Work.Packaging
