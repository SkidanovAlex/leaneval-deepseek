/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RESID (area DM): the residue map

For a curve `C/K`, symmetric powers `symGeom`, a `K`-scheme `X` and morphisms
`a : X ⟶ Sym^r C`, `b : X ⟶ Sym^{r+m} C`, this file constructs the *residue map*
`σ : X ⤏ Sym^m C` whose value at a point `p` of `X` is the effective representative of the
class of the divisor `divOf (b p) - divOf (a p)`.

The construction is by the generic point: `divD symGeom a b p₀` (for `p₀` the generic point of
`X`) has degree `m ≥ g`, so by `RR7` it is linearly equivalent to an effective divisor `E` of
degree `m`, which is `divOf y₀` for some point `y₀` of `Sym^m C` over `K(X)`.  The residue map
is the rational map with generic fibre `y₀` (Mathlib's
`RationalMap.ofFunctionField`), and its generic fibre is `y₀` by construction.

`RR7` is taken as a named hypothesis, in exactly the form of the field `rr7` of
`Work.GroupChunk.Input`.
-/
import Submission.Work.Domain.Resid.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.Domain.Resid

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} [SpecLin.DivBase C]

noncomputable section

variable {symGeom : ∀ n, SpecLin.SymGeom C n} {g : ℕ}

/-! ## The generic value -/

/-- The degree of `divD symGeom a b p` is `m`. -/
theorem ddeg_divD {X : Sch K} {r m : ℕ} (a : X ⟶ (symGeom r).S)
    (b : X ⟶ (symGeom (r + m)).S) {F : Type u} [Field F] [Algebra K F] (p : FPt X F) :
    Ddeg C F (divD symGeom a b p) = (m : ℤ) := by
  have h1 : Ddeg C F ((symGeom (r + m)).divOf (p ≫ b)) = ((r + m : ℕ) : ℤ) :=
    (symGeom (r + m)).divOf_deg (p ≫ b)
  have h2 : Ddeg C F ((symGeom r).divOf (p ≫ a)) = ((r : ℕ) : ℤ) :=
    (symGeom r).divOf_deg (p ≫ a)
  rw [divD, map_sub, h1, h2, Nat.cast_add]
  ring

/-- **The generic value.**  For `m ≥ g`, the class of the generic value `divD a b p₀` is
represented by an effective divisor of degree `m`, hence by a point of `Sym^m C` over the
function field of `X`. -/
theorem exists_genValue {X : Sch K} [IsIntegral X.left] {r m : ℕ}
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    (rr7 : ∀ {F : Type u} [Field F] [Algebra K F] (A : Dv C F), (g : ℤ) ≤ Ddeg C F A →
      ∃ E : Dv C F, E.IsEffective ∧ Ddeg C F E = Ddeg C F A ∧ LinEquiv C A E)
    (hm : g ≤ m) :
    ∃ y : FPt (symGeom m).S X.left.functionField,
      Rel symGeom a b (genericFPt X) y := by
  obtain ⟨E, hEeff, hEdeg, hElin⟩ := rr7 (divD symGeom a b (genericFPt X)) (by
    rw [ddeg_divD a b (genericFPt X)]
    exact_mod_cast hm)
  obtain ⟨y, hy⟩ := (symGeom m).divOf_complete E hEeff
    (show Ddeg C X.left.functionField E = (m : ℤ) from by
      rw [hEdeg, ddeg_divD a b (genericFPt X)])
  exact ⟨y, by rw [rel_iff, hy]; exact hElin.symm⟩

/-- The generic value of the residue map: a point of `Sym^m C` over `K(X)` representing the
class of `divD symGeom a b p₀`. -/
def genValue {X : Sch K} [IsIntegral X.left] {r m : ℕ}
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    (rr7 : ∀ {F : Type u} [Field F] [Algebra K F] (A : Dv C F), (g : ℤ) ≤ Ddeg C F A →
      ∃ E : Dv C F, E.IsEffective ∧ Ddeg C F E = Ddeg C F A ∧ LinEquiv C A E)
    (hm : g ≤ m) : FPt (symGeom m).S X.left.functionField :=
  Classical.choose (exists_genValue a b rr7 hm)

/-- The defining property of `genValue`. -/
theorem genValue_spec {X : Sch K} [IsIntegral X.left] {r m : ℕ}
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    (rr7 : ∀ {F : Type u} [Field F] [Algebra K F] (A : Dv C F), (g : ℤ) ≤ Ddeg C F A →
      ∃ E : Dv C F, E.IsEffective ∧ Ddeg C F E = Ddeg C F A ∧ LinEquiv C A E)
    (hm : g ≤ m) :
    Rel symGeom a b (genericFPt X) (genValue a b rr7 hm) :=
  Classical.choose_spec (exists_genValue a b rr7 hm)

/-! ## The residue map -/

/-- A Mathlib gap: the generic fibre of a composition. -/
theorem fromFunctionField_compHom {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⤏ Y) (h : Y ⟶ Z) :
    (f.compHom h).fromFunctionField = f.fromFunctionField ≫ h := by
  obtain ⟨f₀, rfl⟩ := f.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap f₀ h]
  simp only [Scheme.RationalMap.fromFunctionField_toRationalMap, Scheme.PartialMap.fromFunctionField,
    Scheme.PartialMap.fromSpecStalkOfMem_compHom]

/-- **The residue map.**  The rational map `X ⤏ Sym^m C` with generic fibre `genValue`, i.e.
the rational map whose value at `p` is the effective representative of the class of
`divOf (b p) - divOf (a p)`. -/
def residMap {X : Sch K} [IsIntegral X.left] {r m : ℕ}
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    (rr7 : ∀ {F : Type u} [Field F] [Algebra K F] (A : Dv C F), (g : ℤ) ≤ Ddeg C F A →
      ∃ E : Dv C F, E.IsEffective ∧ Ddeg C F E = Ddeg C F A ∧ LinEquiv C A E)
    (hm : g ≤ m) (hlft : LocallyOfFiniteType ((symGeom m).S).hom) :
    X.left ⤏ (symGeom m).S.left := by
  haveI := hlft
  exact Scheme.RationalMap.ofFunctionField (Over.hom X)
    (Over.hom ((symGeom m).S)) (genValue a b rr7 hm).left
    ((genValue a b rr7 hm).w.trans (specOf_functionField_hom X))

/-- The generic fibre of the residue map is its generic value. -/
theorem residMap_fromFunctionField {X : Sch K} [IsIntegral X.left] {r m : ℕ}
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    (rr7 : ∀ {F : Type u} [Field F] [Algebra K F] (A : Dv C F), (g : ℤ) ≤ Ddeg C F A →
      ∃ E : Dv C F, E.IsEffective ∧ Ddeg C F E = Ddeg C F A ∧ LinEquiv C A E)
    (hm : g ≤ m) (hlft : LocallyOfFiniteType ((symGeom m).S).hom) :
    (residMap (g := g) a b rr7 hm hlft).fromFunctionField = (genValue a b rr7 hm).left :=
  Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _

/-- The residue map is a morphism over `K`. -/
theorem residMap_isOver {X : Sch K} [IsIntegral X.left] {r m : ℕ}
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    (rr7 : ∀ {F : Type u} [Field F] [Algebra K F] (A : Dv C F), (g : ℤ) ≤ Ddeg C F A →
      ∃ E : Dv C F, E.IsEffective ∧ Ddeg C F E = Ddeg C F A ∧ LinEquiv C A E)
    (hm : g ≤ m) (hlft : LocallyOfFiniteType ((symGeom m).S).hom) :
    (residMap (g := g) a b rr7 hm hlft).IsOver (Spec (CommRingCat.of K)) := by
  rw [Scheme.RationalMap.isOver_iff]
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [fromFunctionField_compHom, residMap_fromFunctionField]
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
  rw [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap]
  exact (genValue a b rr7 hm).w.trans (specOf_functionField_hom X)

end

end Work.Domain.Resid
