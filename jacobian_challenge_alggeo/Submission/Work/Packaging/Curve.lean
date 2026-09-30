/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area P (packaging)
-/
import Mathlib
import Submission.Work.Packaging.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Area P: the Abel–Jacobi map of a package

Given a `JacPkg C P0` (a Jacobian package based at `P0`) and an arbitrary `k`-point `P` of `C`, this
file defines the Abel–Jacobi map `ofCurve P` based at `P`,

`ofCurve P = AJ₀ - toUnit C ≫ P ≫ AJ₀`

(computed in the pointwise group `Hom(C, J)`), shows that it sends `P` to the origin, and provides
the `Hom`-level algebra used in `Work.Packaging.Univ` to reduce the universal property for `P` to
the one for `P0`.

The definition is written using `GrpObj.mulRight`, the translation by a point of a group object:
`ofCurve P = AJ₀ ≫ (mulRight (P ≫ AJ₀)⁻¹).hom`. This form is a composite, which makes the transport
of factorisations through it immediate (`Work.Packaging.exists_unique_factor_ofCurve`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped MonObj

namespace Work.Packaging

variable {k : Type u} [Field k]

section HomGroup

/-- The unit of the pointwise group `Hom(𝟙_, G)` is `η[G]`. -/
theorem one_eq_eta {G : Over (Spec (.of k))} [GrpObj G] :
    (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G) = η[G] := by
  rw [Hom.one_def]
  simp

/-- The point `η` of a group object is its own inverse. -/
theorem eta_inv {G : Over (Spec (.of k))} [GrpObj G] : η[G]⁻¹ = η[G] := by
  rw [← one_eq_eta, inv_one]

/-- Right translation by a point `b` of a group object, on morphisms `H ⟶ G`. -/
theorem comp_mulRight_hom {H G : Over (Spec (.of k))} [GrpObj G] (f : H ⟶ G)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    f ≫ (GrpObj.mulRight b).hom = f * (toUnit H ≫ b) := by
  rw [GrpObj.mulRight_hom, ← Category.assoc, comp_lift, Hom.mul_def]
  congr 1
  rw [Category.comp_id, ← Category.assoc, comp_toUnit]

/-- Right translation by a point, on points. -/
theorem point_mulRight {G : Over (Spec (.of k))} [GrpObj G]
    (a b : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    a ≫ (GrpObj.mulRight b).hom = a * b := by
  rw [comp_mulRight_hom, toUnit_unit, Category.id_comp]

end HomGroup

section OfCurve

variable {C : Over (Spec (.of k))} {P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C}

/-- The Abel–Jacobi map of the package `Pkg` based at the `k`-point `P`: the composite
`AJ₀ ≫ (· + (P ≫ AJ₀))⁻¹`, i.e. `AJ₀ - toUnit C ≫ P ≫ AJ₀` in the pointwise group `Hom(C, J)`. -/
noncomputable def ofCurve (Pkg : JacPkg C P0) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : C ⟶ Pkg.J :=
  Pkg.AJ₀ ≫ (GrpObj.mulRight (A := Pkg.J) (P ≫ Pkg.AJ₀)⁻¹).hom

/-- `ofCurve P` is the translate of `AJ₀` by the point `P ≫ AJ₀`. -/
theorem ofCurve_eq_div (Pkg : JacPkg C P0) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    ofCurve Pkg P = Pkg.AJ₀ / (toUnit C ≫ (P ≫ Pkg.AJ₀)) := by
  rw [ofCurve, comp_mulRight_hom, div_eq_mul_inv, GrpObj.comp_inv]

/-- `ofCurve P` sends `P` to the origin. -/
theorem comp_ofCurve (Pkg : JacPkg C P0) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ ofCurve Pkg P = η[Pkg.J] := by
  rw [ofCurve, ← Category.assoc, point_mulRight, mul_inv_cancel, one_eq_eta]

/-- `ofCurve` at the base point `P0` is `AJ₀` itself. -/
theorem ofCurve_basePoint (Pkg : JacPkg C P0) : ofCurve Pkg P0 = Pkg.AJ₀ := by
  rw [ofCurve, Pkg.AJ₀_pt, eta_inv, GrpObj.mulRight_one, Iso.refl_hom, Category.comp_id]

/-- The translation isomorphism used to pass between `AJ₀` and `ofCurve P`. -/
noncomputable def ofCurveIso (Pkg : JacPkg C P0) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    Pkg.J ≅ Pkg.J :=
  GrpObj.mulRight (A := Pkg.J) (P ≫ Pkg.AJ₀)⁻¹

theorem ofCurve_eq_comp_iso (Pkg : JacPkg C P0) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    ofCurve Pkg P = Pkg.AJ₀ ≫ (ofCurveIso Pkg P).hom := rfl

end OfCurve

end Work.Packaging
