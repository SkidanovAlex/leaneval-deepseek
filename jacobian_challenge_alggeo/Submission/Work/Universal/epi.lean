/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area UP: `AJ₀` is an epimorphism

The Abel–Jacobi map `AJ₀ : C ⟶ G D` is an epimorphism onto abelian varieties: two morphisms
`u v : G D ⟶ A` with `AJ₀ ≫ u = AJ₀ ≫ v` are equal.

The proof follows the blueprint (`NOTES_LEAD_jacobian_GC.md` §3.8, "Uniqueness = epi"):

* `u' := u - u(0)` is pointed, and since `G D` is proper and geometrically integral and `A` is an
  abelian variety, `u'` is a homomorphism of group schemes (`Work.AbVar.Hom.isMonHom_of_isPointedMap`);
  similarly `v' := v - v(0)`.
* `AJ₀ ≫ u' = AJ₀ ≫ v'` by the hypothesis and `AJ₀(P0) = η`.
* Hence, composing with `AJSym = Σ^g AJ₀` and using that composing `sumMap` with a monoid
  homomorphism is `sumMap` of the composite, `AJSym ≫ u' = AJSym ≫ v'`.
* `AJSym` is surjective and `A` is separated, so `u' = v'`
  (`Work.AbVar.eq_of_surjective`).
* Finally `u = u' + u(0)`, `v = v' + v(0)` and `u(0) = v(0)` from `P0 ≫ AJ₀ = η`.

-/
import Mathlib
import Submission.Work.Universal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open Work.GCBasics
open scoped Work.GCBasics

namespace Work.Universal

noncomputable section

universe u

variable {K : Type u} [Field K] {C : CurveBasics.Curve K}
  {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]

/-! ## 1. `sumMap` composed with a monoid homomorphism -/

/-- Composing the sum morphism `Σᵐ f` with a monoid homomorphism is the sum morphism of the
composite: `(Σᵐ f) ≫ h = Σᵐ (f ≫ h)`.  Proved directly from the uniqueness part of
`sumMap_unique`, using that a finite product of morphisms composes with a monoid homomorphism
(`prod_comp`). -/
theorem sumMap_comp_isMonHom (D : GroupChunk.Input C P0) [SymQuotData C P0 D]
    {A B : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [GrpObj B] [IsCommMonObj B]
    (f : C.toOver ⟶ A) (h : A ⟶ B) [IsMonHom h] (n : ℕ) :
    sumMap D f n ≫ h = sumMap D (f ≫ h) n := by
  refine sumMap_unique D (f ≫ h) n ?_
  rw [← Category.assoc, sumMap_spec]
  simp only [sumTerm]
  rw [prod_comp]
  simp only [Category.assoc]

/-! ## 2. The pointed part of a morphism `G ⟶ A` -/

/-- The translate of `w : G ⟶ A` by `w(0)`: the morphism `x ↦ w(x) · w(0)⁻¹`, i.e. the
"pointed part" of `w`. -/
def ptPart {G A : Sch K} [GrpObj G] [GrpObj A] (w : G ⟶ A) : G ⟶ A :=
  w / (toUnit G ≫ (η[G] ≫ w))

/-- The pointed part of `w` is pointed: it sends the origin of `G` to the origin of `A`. -/
theorem ptPart_isPointed {G A : Sch K} [GrpObj G] [GrpObj A] (w : G ⟶ A) :
    η[G] ≫ ptPart w = η[A] := by
  rw [ptPart, GrpObj.comp_div]
  have hc : η[G] ≫ (toUnit G ≫ (η[G] ≫ w)) = η[G] ≫ w := by
    rw [← Category.assoc (η[G]) (toUnit G) (η[G] ≫ w)]
    have h : η[G] ≫ toUnit G = 𝟙 (𝟙_ (Sch K)) := toUnit_unique _ _
    rw [h, Category.id_comp]
  rw [hc, div_self']
  exact (MonObj.one_eq_one A).symm

/-- **A pointed morphism from a proper, geometrically integral group scheme to an abelian
variety is a homomorphism of group schemes.**  This is
`Work.AbVar.Hom.isMonHom_of_isPointedMap` (the rigidity lemma). -/
theorem ptPart_isMonHom {G A : Sch K} [GrpObj G] [GrpObj A] [IsProper G.hom]
    [GeometricallyIntegral G.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] (w : G ⟶ A) :
    IsMonHom (ptPart w) :=
  Work.AbVar.Hom.isMonHom_of_isPointedMap (ptPart w) (ptPart_isPointed w)

/-- `w` is its pointed part composed with the translate by `w(0)`. -/
theorem ptPart_mul_self {G A : Sch K} [GrpObj G] [GrpObj A] (w : G ⟶ A) :
    ptPart w * (toUnit G ≫ (η[G] ≫ w)) = w :=
  div_mul_cancel w _

end

/-! ## 3. The epimorphism statement -/

theorem epi {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] [U : Work.Universal.Input C P0]
    {A : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [Work.AbVar.IsAbelianVariety A]
    (u v : U.glued.G ⟶ A)
    (h : CategoryTheory.CategoryStruct.comp U.AJ₀ u
      = CategoryTheory.CategoryStruct.comp U.AJ₀ v) : u = v := by
  -- `u(0) = v(0)`, from `P0 ≫ AJ₀ = η`.
  have hpt : η[U.glued.G] ≫ u = η[U.glued.G] ≫ v := by
    calc η[U.glued.G] ≫ u = (P0 ≫ U.AJ₀) ≫ u := by rw [U.AJ₀_pt]
      _ = P0 ≫ (U.AJ₀ ≫ u) := by rw [Category.assoc]
      _ = P0 ≫ (U.AJ₀ ≫ v) := by rw [h]
      _ = (P0 ≫ U.AJ₀) ≫ v := by rw [Category.assoc]
      _ = η[U.glued.G] ≫ v := by rw [U.AJ₀_pt]
  -- The translates by `u(0)` and `v(0)` agree after composing with `AJ₀`.
  have hc : U.AJ₀ ≫ (toUnit U.glued.G ≫ (η[U.glued.G] ≫ u))
      = U.AJ₀ ≫ (toUnit U.glued.G ≫ (η[U.glued.G] ≫ v)) := by
    rw [← Category.assoc U.AJ₀ (toUnit U.glued.G) (η[U.glued.G] ≫ u),
      ← Category.assoc U.AJ₀ (toUnit U.glued.G) (η[U.glued.G] ≫ v),
      SemiCartesianMonoidalCategory.comp_toUnit, hpt]
  have hAJ : U.AJ₀ ≫ ptPart u = U.AJ₀ ≫ ptPart v := by
    simp only [ptPart]
    rw [GrpObj.comp_div, GrpObj.comp_div, h, hc]
  -- Both pointed parts are monoid homomorphisms, so `AJSym` (a sum of `AJ₀`) separates them.
  have hAJSym : U.AJSym ≫ ptPart u = U.AJSym ≫ ptPart v := by
    have hum : IsMonHom (ptPart u) := ptPart_isMonHom u
    have hvm : IsMonHom (ptPart v) := ptPart_isMonHom v
    have hu : U.AJSym ≫ ptPart u = sumMap D (U.AJ₀ ≫ ptPart u) D.g := by
      rw [U.AJSym_eq_sumMap]
      exact sumMap_comp_isMonHom D U.AJ₀ (ptPart u) D.g
    have hv : U.AJSym ≫ ptPart v = sumMap D (U.AJ₀ ≫ ptPart v) D.g := by
      rw [U.AJSym_eq_sumMap]
      exact sumMap_comp_isMonHom D U.AJ₀ (ptPart v) D.g
    rw [hu, hv, hAJ]
  have huv : ptPart u = ptPart v :=
    Work.AbVar.eq_of_surjective U.AJSym ⟨U.AJSym_surjective⟩ hAJSym
  -- Assemble: `u = u' + u(0) = v' + v(0) = v`.
  calc u = ptPart u * (toUnit U.glued.G ≫ (η[U.glued.G] ≫ u)) := (ptPart_mul_self u).symm
    _ = ptPart v * (toUnit U.glued.G ≫ (η[U.glued.G] ≫ u)) := by rw [huv]
    _ = ptPart v * (toUnit U.glued.G ≫ (η[U.glued.G] ≫ v)) := by rw [hpt]
    _ = v := ptPart_mul_self v

end Work.Universal
