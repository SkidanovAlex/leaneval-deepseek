/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area P (packaging)
-/
import Mathlib
import Submission.Work.Packaging.Basic
import Submission.Work.Packaging.Curve

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Area P: the universal property at an arbitrary base point

We prove that the universal property of the package `JacPkg C P0` for the base point `P0`
(the field `JacPkg.univ₀`) implies the universal property for *every* `k`-point `P` of `C`, with
`ofCurve P := AJ₀ - toUnit C ≫ P ≫ AJ₀` in place of `AJ₀`.

The translation from `P0` to `P` is pure algebra of the pointwise group `Hom(C, ·)`:

* existence: `f / (toUnit C ≫ (P0 ≫ f))` is pointed at `P0`, so it factors as `AJ₀ ≫ g'`; then
  `f = AJ₀ ≫ (g' * (toUnit J ≫ (P0 ≫ f)))`, and `ofCurve P = AJ₀ ≫ τ` with `τ` an isomorphism, so
  `f = ofCurve P ≫ (τ⁻¹ ≫ (g' * (toUnit J ≫ (P0 ≫ f))))`;
* uniqueness: `ofCurve P ≫ g = AJ₀ ≫ (τ ≫ g)`, and `epi₀` (the package field) says that
  `w ↦ AJ₀ ≫ w` is injective.

In particular *no* pointedness hypothesis on `f` is needed: every `f : C ⟶ A` into an abelian
variety factors uniquely through `ofCurve P`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped MonObj

namespace Work.Packaging

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C}

/-- `AJ₀` respects constant maps: the composite of `AJ₀` with the constant map at a point `c` of the
target is the constant map at `c` on `C`. -/
theorem AJ₀_comp_const (Pkg : JacPkg C P0) {A : Over (Spec (.of k))}
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    Pkg.AJ₀ ≫ (toUnit Pkg.J ≫ c) = toUnit C ≫ c := by
  rw [← Category.assoc, comp_toUnit]

/-- Every morphism `f : C ⟶ A` into an abelian variety factors through `AJ₀` (as a morphism of
schemes over `Spec k`, with no condition at the base point). -/
theorem exists_comp_AJ₀ (Pkg : JacPkg C P0) {A : Over (Spec (.of k))} [Smooth A.hom]
    [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A] (f : C ⟶ A) :
    ∃ w : Pkg.J ⟶ A, f = Pkg.AJ₀ ≫ w := by
  have hc : P0 ≫ (toUnit C ≫ (P0 ≫ f)) = P0 ≫ f := by
    rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  have hpt : P0 ≫ (f / (toUnit C ≫ (P0 ≫ f))) = η[A] := by
    rw [GrpObj.comp_div, hc, div_eq_mul_inv, mul_inv_cancel, one_eq_eta]
  obtain ⟨g', hg', -⟩ := Pkg.univ₀ A (f / (toUnit C ≫ (P0 ≫ f))) hpt
  refine ⟨g' * (toUnit Pkg.J ≫ (P0 ≫ f)), ?_⟩
  have hAJ : f = Pkg.AJ₀ ≫ (g' * (toUnit Pkg.J ≫ (P0 ≫ f))) := by
    rw [MonObj.comp_mul, ← hg', AJ₀_comp_const, div_eq_mul_inv, _root_.mul_assoc,
      _root_.inv_mul_cancel, _root_.mul_one]
  exact hAJ

/-- `ofCurve P ≫ g = AJ₀ ≫ (σ ≫ g)` where `σ` is the translating isomorphism. -/
theorem comp_ofCurve_iso_assoc (Pkg : JacPkg C P0) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} (g : Pkg.J ⟶ A) :
    ofCurve Pkg P ≫ g = Pkg.AJ₀ ≫ ((ofCurveIso Pkg P).hom ≫ g) := by
  rw [ofCurve_eq_comp_iso, Category.assoc]

/-- The universal property of the package at an arbitrary base point `P`, without pointedness. -/
theorem exists_unique_factor_ofCurve (Pkg : JacPkg C P0)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom]
    [GeometricallyIrreducible A.hom] [GrpObj A] (f : C ⟶ A) :
    ∃! g : Pkg.J ⟶ A, f = ofCurve Pkg P ≫ g := by
  obtain ⟨w, hw⟩ := exists_comp_AJ₀ Pkg f
  have key : ∀ g : Pkg.J ⟶ A, f = ofCurve Pkg P ≫ g ↔ (ofCurveIso Pkg P).hom ≫ g = w := by
    intro g
    constructor
    · intro h
      refine Pkg.epi₀ A _ w ?_
      rw [← comp_ofCurve_iso_assoc, ← h]
      exact hw
    · intro h
      rw [comp_ofCurve_iso_assoc, h, hw]
  refine ⟨(ofCurveIso Pkg P).inv ≫ w, ?_, ?_⟩
  · refine (key _).mpr ?_
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · intro g hg
    have h := (key g).mp hg
    calc g = 𝟙 _ ≫ g := by rw [Category.id_comp]
      _ = ((ofCurveIso Pkg P).inv ≫ (ofCurveIso Pkg P).hom) ≫ g := by rw [Iso.inv_hom_id]
      _ = (ofCurveIso Pkg P).inv ≫ ((ofCurveIso Pkg P).hom ≫ g) := by rw [Category.assoc]
      _ = (ofCurveIso Pkg P).inv ≫ w := by rw [h]

/-- The universal property of the package at an arbitrary base point `P`, in the form required by
the challenge: `f` is assumed to send `P` to the origin. -/
theorem exists_unique_ofCurve_comp (Pkg : JacPkg C P0) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom]
    [GrpObj A] (f : C ⟶ A) (_hf : P ≫ f = η[A]) :
    ∃! g : Pkg.J ⟶ A, f = ofCurve Pkg P ≫ g :=
  exists_unique_factor_ofCurve Pkg P f

end Work.Packaging
