/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The place attached to a `k`-point of a curve has degree one

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k` and let
`p : Spec k ⟶ C` be a `k`-point of `C`.  Its image is a closed point `Q = placeOfPoint C p`
of `C` (a *place*), and this file computes its degree:

> `Q.degree = [κ(Q) : k] = 1`.

Equivalently: the residue field of a `k`-rational point of `C` is `k` itself.

## Proof

Write `f = C.hom : C.left ⟶ Spec k` for the structure morphism, `s = Pt.leftHom p` for the
`k`-point, and `z = IsLocalRing.closedPoint k` for the closed point of `Spec k`, so that
`Q.point = s z`.  Since `s` is a section of `f` (`s ≫ f = 𝟙 (Spec k)`), the maps on residue
fields fit into a commutative triangle

`κ(z) --φ--> κ(s z) --ψ--> κ(z)`,  with `ψ ∘ φ = id`  (`φ = f.residueFieldMap (s z)`,
`ψ = s.residueFieldMap z`),

the composite being `(s ≫ f).residueFieldMap z = (𝟙 _).residueFieldMap z`.  Because `Spec k`
is a subsingleton (k being a field) the two points `f (s z)` and `z` are equal, and the
identity `ψ ∘ φ = id` is exactly `f.residueFieldMap (s z) ≫ s.residueFieldMap z =
(Scheme.residueFieldCongr ·).hom`, an isomorphism; in particular `ψ` — a ring homomorphism
of fields — is injective.

Since `residueDegree` is the dimension of `κ(s z)` over `κ(f (s z))` acting through `φ`,
surjectivity of `φ` is what has to be shown, and it follows from the injectivity of `ψ`:
for `w : κ(s z)`, the scalar `c := (Scheme.residueFieldCongr ·).inv (ψ w)` satisfies
`ψ (φ c) = ψ w`, hence `φ c = w`.  So `φ` is onto and the dimension is one.  The lower
bound `1 ≤ residueDegree` is `Work.CurveBasics.Place.residueDegree_pos` (the residue field
is a positive-dimensional extension), and the two bounds meet at `1`.
-/
import Mathlib
import Submission.Work.KeyLemma.Sum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Place

open CategoryTheory AlgebraicGeometry
open scoped Classical

set_option linter.style.haveILetI false

universe u

theorem placeOfPoint_degree {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (p : Work.KeyLemma.Curve.Point C) :
    (Work.KeyLemma.Curve.placeOfPoint C p).degree = 1 := by
  -- The closed point of `Spec k` and the underlying morphism of the `k`-point `p`.
  set z : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  set s : Spec (CommRingCat.of k) ⟶ C.left := Work.KeyLemma.Curve.Pt.leftHom p
  show C.hom.residueDegree (s z) = 1
  -- `s` is a section of the structure morphism of the curve.
  have hsec : s ≫ C.hom = 𝟙 (Spec (CommRingCat.of k)) :=
    Work.KeyLemma.Curve.Pt.leftHom_comp p
  -- `Spec k` has a single point, so `C.hom (s z) = z`.
  have hpoint : C.hom (s z) = z := Subsingleton.elim _ _
  -- Functoriality of residue field maps along the identity `s ≫ C.hom = 𝟙`.
  have hcomp : C.hom.residueFieldMap (s z) ≫ s.residueFieldMap z
      = (Scheme.residueFieldCongr hpoint).hom := by
    rw [← Scheme.residueFieldMap_comp]
    rw [Scheme.Hom.residueFieldMap_congr hsec z]
    simp
  -- The residue degree is positive: `κ(s z)` is a finite extension of `κ(C.hom (s z))`.
  have hpos : 0 < C.hom.residueDegree (s z) :=
    Work.CurveBasics.Place.residueDegree_pos (Work.KeyLemma.Curve.placeOfPoint C p)
  -- The algebra structure used by `Scheme.Hom.residueDegree` at `s z`.
  letI : Algebra ((Spec (CommRingCat.of k)).residueField (C.hom (s z)))
      (C.left.residueField (s z)) := (C.hom.residueFieldMap (s z)).hom.toAlgebra
  -- `s.residueFieldMap z` is a ring homomorphism of fields, hence injective.
  have hψinj : Function.Injective (s.residueFieldMap z) := RingHom.injective _
  have hfin : Module.finrank ((Spec (CommRingCat.of k)).residueField (C.hom (s z)))
      (C.left.residueField (s z)) = 1 := by
    rw [finrank_eq_one_iff_of_nonzero' (1 : C.left.residueField (s z)) one_ne_zero]
    intro w
    -- `φ` is onto: the scalar `c := κ(z) ≅ κ(C.hom (s z))` applied to `s.residueFieldMap z w`
    -- maps to `w`.
    refine ⟨(Scheme.residueFieldCongr hpoint).inv ((s.residueFieldMap z) w), ?_⟩
    rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
    show (C.hom.residueFieldMap (s z))
        ((Scheme.residueFieldCongr hpoint).inv ((s.residueFieldMap z) w)) = w
    refine hψinj ?_
    have hcc := congrArg
      (fun k => k ((Scheme.residueFieldCongr hpoint).inv ((s.residueFieldMap z) w))) hcomp
    rw [CategoryTheory.Iso.inv_hom_id_apply] at hcc
    exact hcc
  -- Combine the two bounds on the residue degree.
  have hle : C.hom.residueDegree (s z) ≤ 1 := by
    rw [Scheme.Hom.residueDegree]
    exact le_of_eq hfin
  omega

end Work.KeyLemma.Place
