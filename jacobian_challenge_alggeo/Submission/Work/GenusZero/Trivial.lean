/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area GenusZero
-/
import Submission.Work.GenusZero.Rigidity
import Submission.Work.Packaging.Trivial

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GenusZero: the Jacobian package at genus zero

At genus zero the Jacobian of a pointed curve `(C, P0)` is the trivial group scheme `𝟙_`, and
the Abel–Jacobi map is the unique morphism `toUnit C : C ⟶ 𝟙_`.  This file assembles the
package `Work.Packaging.JacPkg C P0` from that data:

* `J := 𝟙_ (Sch k)`, with the instances of `Work.Packaging.Trivial` (`GrpObj`, `IsProper`,
  `GeometricallyIrreducible`, `Smooth`, `ConnectedSpace`);
* `AJ₀ := toUnit C`, and `AJ₀_pt` holds because both sides are endomorphisms of the terminal
  object;
* `univ₀`: a pointed `f : C ⟶ A` equals `toUnit C ≫ η[A]` by `Work.GenusZero.eq_const_of_genus_zero`,
  so `η[A]` is a (and the only) factorisation, since `P0 ≫ toUnit C = 𝟙`;
* `epi₀`: two morphisms out of `𝟙_` agreeing after precomposition with `toUnit C` agree, because
  `P0 ≫ toUnit C = 𝟙`.

## Main results

* `Work.GenusZero.jacPkg_of_genus_zero`
-/

set_option autoImplicit false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

universe u

namespace Work.GenusZero

variable {k : Type u} [Field k]

/-- `P0 ≫ toUnit C = 𝟙` for any `k`-point `P0` of a `k`-scheme `C`: both are morphisms to the
terminal object. -/
theorem point_comp_toUnit_eq_id {C : Sch k} (P0 : 𝟙_ (Sch k) ⟶ C) :
    P0 ≫ toUnit C = 𝟙 (𝟙_ (Sch k)) :=
  toUnit_unique _ _

/-- A `k`-point of `C` splits the constant map `toUnit C`: two morphisms out of the terminal
object which agree after precomposition with `toUnit C` agree.  This is the `epi₀` field of the
genus-zero Jacobian package, isolated. -/
theorem eq_of_comp_toUnit_eq {C : Sch k} (P0 : 𝟙_ (Sch k) ⟶ C) {A : Sch k}
    (u v : 𝟙_ (Sch k) ⟶ A) (h : toUnit C ≫ u = toUnit C ≫ v) : u = v := by
  have hP0 : P0 ≫ toUnit C = 𝟙 (𝟙_ (Sch k)) := point_comp_toUnit_eq_id P0
  calc u = 𝟙 (𝟙_ (Sch k)) ≫ u := (Category.id_comp u).symm
    _ = (P0 ≫ toUnit C) ≫ u := by rw [hP0]
    _ = P0 ≫ (toUnit C ≫ u) := Category.assoc _ _ _
    _ = P0 ≫ (toUnit C ≫ v) := by rw [h]
    _ = (P0 ≫ toUnit C) ≫ v := (Category.assoc _ _ _).symm
    _ = 𝟙 (𝟙_ (Sch k)) ≫ v := by rw [hP0]
    _ = v := Category.id_comp v

/-- **The genus-zero Jacobian package.**  For a smooth proper geometrically irreducible curve
`C` over `k` of genus zero and a `k`-point `P0`, the Jacobian package `Work.Packaging.JacPkg C P0`
exists: the Jacobian is the trivial group scheme, and the universal property follows from
rigidity (`Work.GenusZero.eq_const_of_genus_zero`). -/
noncomputable def jacPkg_of_genus_zero (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z))
    (hnt : Nontrivial C.left)
    (hg : RiemannRoch.Curve.genus (CurveBasics.Curve.ofOver C hred hdim hnt) = 0)
    (P0 : 𝟙_ (Sch k) ⟶ C) : Nonempty (Work.Packaging.JacPkg C P0) := by
  refine ⟨{ J := 𝟙_ (Sch k)
            AJ₀ := toUnit C
            AJ₀_pt := toUnit_unique _ _
            univ₀ := ?_
            epi₀ := ?_ }⟩
  · intro A _ _ _ _ f hf
    have hmain : f = toUnit C ≫ η[A] :=
      eq_const_of_genus_zero (CurveBasics.Curve.ofOver C hred hdim hnt) hg P0 f hf
    refine ⟨η[A], hmain, ?_⟩
    intro g hg'
    have h1 : P0 ≫ toUnit C ≫ g = η[A] := by rw [← hg', hf]
    rw [← Category.assoc, point_comp_toUnit_eq_id P0, Category.id_comp] at h1
    exact h1
  · intro A _ _ _ _ u v huv
    exact eq_of_comp_toUnit_eq P0 u v huv

/-- **The genus-zero branch of the single input of the challenge**, in the shape in which
`Work.JacFinal.jacPkgExists` needs it: for *every* `k`-point `P0` of a curve of genus zero, the
Jacobian package exists. -/
theorem jacPkgExists_of_genus_zero (C : Work.GenusZero.Sch k)
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 C.hom]
    [AlgebraicGeometry.IsProper C.hom]
    [AlgebraicGeometry.GeometricallyIrreducible C.hom]
    (hred : AlgebraicGeometry.GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z))
    (hnt : Nontrivial C.left)
    (hg : RiemannRoch.Curve.genus (CurveBasics.Curve.ofOver C hred hdim hnt) = 0) :
    ∀ P0 : 𝟙_ (Work.GenusZero.Sch k) ⟶ C, Nonempty (Work.Packaging.JacPkg C P0) :=
  fun P0 => jacPkg_of_genus_zero C hred hdim hnt hg P0

end Work.GenusZero
