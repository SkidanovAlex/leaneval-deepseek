/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL, layer 2: the sum of a multiset of points of a curve in an abelian variety

The key lemma `KL` asks for the sum `Σ f(D) ∈ A(F)` of the images under `f : C ⟶ A` of the
points of an effective divisor `D` on `C`.  This file builds the *split* (or "model") form
of that sum, which is what the geometric argument actually computes with:

* `Point C` is the set of `k`-points of the curve `C`, i.e. morphisms `Spec k ⟶ C` over
  `Spec k`;
* `SumDiv C = (Point C) →₀ ℕ` is the type of *multisets of `k`-points* of `C`, i.e. the
  effective divisors of `C` which are split over `k`, presented together with their points;
* `SumDiv.placeOfPoint C p` is the closed point (place) which is the image of the `k`-point
  `p`; the image is closed because a `k`-point is a section of the proper (hence separated)
  morphism `C ⟶ Spec k` (`isClosedImmersion_of_comp_eq_id`);
* `SumDiv.toDiv C s` is the effective divisor `∑_p s p · [placeOfPoint p]` attached to a
  multiset;
* `SumDiv.sumOfPoints C f s = ∏_p (p ≫ f) ^ (s p)` is the sum of the images of the points
  of `s` in the commutative group `A(k)` of `k`-points of `A`, for `A` a commutative group
  scheme over `k` (`IsCommMonObj`, which holds for abelian varieties).

The sum `sumOfPoints` is *not* a function of the divisor `toDiv C s` on the nose: two
multisets with the same underlying divisor could a priori have different sums, and the
statement that they do not -- that a `k`-rational point of a curve is determined by its
image -- is the lemma
`Work.KeyLemma.Curve.SumDiv.eq_of_toDiv_eq` (and its strengthening `toDiv_injective`),
which is proved in `Submission/Work/KeyLemma/Sum/` (see `NOTES.md`).

## Main definitions

* `Work.KeyLemma.Curve.Point`, `Work.KeyLemma.Curve.SumDiv`
* `Work.KeyLemma.Curve.SumDiv.placeOfPoint`
* `Work.KeyLemma.Curve.SumDiv.toDiv`
* `Work.KeyLemma.Curve.SumDiv.sumOfPoints`

## Main results

* `Work.KeyLemma.Curve.SumDiv.toDiv_add`, `…toDiv_zero`
* `Work.KeyLemma.Curve.SumDiv.sumOfPoints_add`, `…sumOfPoints_zero`, `…sumOfPoints_single`
* `Work.KeyLemma.Curve.SumDiv.sumOfPoints_of_toDiv_eq` (linearity in the divisor)
-/
import Submission.Work.KeyLemma.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-! ## Points of a `k`-scheme and points of a curve -/

/-- The `k`-points of a `k`-scheme `X`: morphisms `Spec k ⟶ X` over `Spec k`. -/
abbrev Pt (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))) : Type u :=
  𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X

/-- The `k`-points of a curve. -/
abbrev Point (C : Curve k) : Type u := Pt k C.toOver

namespace Pt

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}

/-- A `k`-point of a `k`-scheme `X`, viewed as a morphism of schemes `Spec k ⟶ X`. -/
abbrev leftHom (p : Pt k X) : Spec (CommRingCat.of k) ⟶ X.left := Over.Hom.left p

/-- A `k`-point of `X` is a section of the structure morphism of `X`. -/
theorem leftHom_comp (p : Pt k X) : leftHom p ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [leftHom, Over.w p]
  rfl

end Pt

/-- A `k`-point of a curve is a section of the structure morphism; since a proper curve is
separated, it is a closed immersion, hence has closed image. -/
theorem isClosedImmersion_of_point (C : Curve k) (p : Point C) :
    IsClosedImmersion (Pt.leftHom p) := by
  have hsec : Pt.leftHom p ≫ C.hom = 𝟙 (Spec (CommRingCat.of k)) := Pt.leftHom_comp p
  exact isClosedImmersion_of_comp_eq_id C.hom (Pt.leftHom p) hsec

theorem isClosed_range_of_point (C : Curve k) (p : Point C) :
    IsClosed (Set.range (Pt.leftHom p)) :=
  (IsClosedImmersion.isClosedEmbedding (Pt.leftHom p)).isClosed_range

/-- The image of a `k`-point of a curve is its only point, `Spec k` having a single point. -/
theorem range_leftHom_eq_singleton (C : Curve k) (p : Point C) :
    Set.range (Pt.leftHom p) = {Pt.leftHom p (IsLocalRing.closedPoint k)} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Set.mem_singleton_iff]
    exact congrArg (Pt.leftHom p) (Subsingleton.elim z _)
  · intro hy
    exact ⟨_, hy.symm⟩

/-- The image of a `k`-point of a curve, as a closed point: a *place* of the curve. -/
noncomputable def placeOfPoint (C : Curve k) (p : Point C) : C.Place :=
  ⟨Pt.leftHom p (IsLocalRing.closedPoint k), by
    rw [mem_closedPoints_iff, ← range_leftHom_eq_singleton C p]
    exact isClosed_range_of_point C p⟩

@[simp]
theorem placeOfPoint_point (C : Curve k) (p : Point C) :
    (placeOfPoint C p).point = Pt.leftHom p (IsLocalRing.closedPoint k) := rfl

/-! ## Multisets of points -/

/-- The type of *multisets of `k`-points* of a curve: an effective divisor of `C` which is
split over `k`, presented by its points. -/
abbrev SumDiv (C : Curve k) : Type u := Point C →₀ ℕ

namespace SumDiv

variable {C : Curve k}

/-- The number of points of a multiset, counted with multiplicity. -/
def deg (s : SumDiv C) : ℕ := s.sum (fun _ m => m)

/-- The multiplicity of the multiset `s` at the place `Q`, i.e. the coefficient of `Q` in
the divisor `toDiv C s`, as an integer. -/
def coeffAt (s : SumDiv C) (Q : C.Place) : ℤ :=
  s.sum (fun p m => if placeOfPoint C p = Q then (m : ℤ) else 0)

/-- The effective divisor attached to a multiset of `k`-points of `C`. -/
noncomputable def toDiv (C : Curve k) (s : SumDiv C) : C.Div :=
  s.sum (fun p m => (Finsupp.single (placeOfPoint C p) (m : ℤ) : C.Div))

theorem toDiv_apply (C : Curve k) (s : SumDiv C) (Q : C.Place) :
    toDiv C s Q = coeffAt s Q := by
  rw [toDiv, Finsupp.sum_apply, coeffAt]
  exact Finsupp.sum_congr fun p _ => by rw [Finsupp.single_apply]

theorem toDiv_zero (C : Curve k) : toDiv C 0 = 0 := by
  rw [toDiv, Finsupp.sum_zero_index]

theorem toDiv_add (C : Curve k) (s t : SumDiv C) :
    toDiv C (s + t) = toDiv C s + toDiv C t :=
  Finsupp.sum_add_index' (fun a => by simp)
    (fun a b₁ b₂ => by rw [Nat.cast_add, Finsupp.single_add])

/-- The "sum" of the divisorial parts: `toDiv` is additive. -/
noncomputable def toDivAddHom (C : Curve k) : SumDiv C →+ C.Div where
  toFun := toDiv C
  map_zero' := toDiv_zero C
  map_add' := toDiv_add C

@[simp]
theorem toDivAddHom_apply (C : Curve k) (s : SumDiv C) : toDivAddHom C s = toDiv C s := rfl

theorem coeffAt_nonneg (s : SumDiv C) (Q : C.Place) : 0 ≤ coeffAt s Q := by
  rw [coeffAt, Finsupp.sum]
  exact Finset.sum_nonneg fun p _ => by split <;> simp

theorem toDiv_isEffective (C : Curve k) (s : SumDiv C) : (toDiv C s).IsEffective := by
  intro Q
  rw [toDiv_apply]
  exact coeffAt_nonneg s Q

/-- The sum of the images in `A` of the points of a multiset of points of `C`, where `A` is
a commutative group scheme over `k` and `f : C ⟶ A` is a morphism. -/
noncomputable def sumOfPoints (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (s : SumDiv C) : Pt k A :=
  s.prod (fun p m => (p ≫ f) ^ m)

@[simp]
theorem sumOfPoints_zero (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) : sumOfPoints C f 0 = 1 :=
  Finsupp.prod_zero_index

theorem sumOfPoints_add (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (s t : SumDiv C) :
    sumOfPoints C f (s + t) = sumOfPoints C f s * sumOfPoints C f t :=
  Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _)

@[simp]
theorem sumOfPoints_single (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (p : Point C) (m : ℕ) :
    sumOfPoints C f (Finsupp.single p m) = (p ≫ f) ^ m :=
  Finsupp.prod_single_index (pow_zero _)

@[simp]
theorem sumOfPoints_single_one (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (p : Point C) :
    sumOfPoints C f (Finsupp.single p 1) = p ≫ f := by
  rw [sumOfPoints_single, pow_one]

/-- If a multiset of points of `C` is determined by the divisor it defines -- i.e. if
`toDiv` is injective -- then the sum of its images depends only on that divisor.  This is
the form in which the well-definedness of `Σ f(D)` is used. -/
theorem sumOfPoints_of_toDiv_eq (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A)
    (hinj : Function.Injective (toDiv C)) {s t : SumDiv C}
    (h : toDiv C s = toDiv C t) : sumOfPoints C f s = sumOfPoints C f t := by
  rw [hinj h]

end SumDiv

/-- An effective divisor of a curve is *split over `k`* if every point of its support is
the image of a `k`-point of the curve.  Equivalently, it is the divisor of a multiset of
`k`-points, i.e. it lies in the image of `SumDiv.toDiv`. -/
def IsSplit (C : Curve k) (D : C.Div) : Prop :=
  ∀ Q ∈ D.support, ∃ p : Point C, placeOfPoint C p = Q

theorem IsSplit.mono {C : Curve k} {D E : C.Div} (hD : D.IsEffective) (h : IsSplit C E)
    (hDE : ∀ Q, D Q ≤ E Q) : IsSplit C D := by
  intro Q hQ
  refine h Q ?_
  rw [Finsupp.mem_support_iff] at hQ ⊢
  intro h0
  have hle2 : E Q ≤ D Q := by rw [h0]; exact hD Q
  exact hQ ((le_antisymm (hDE Q) hle2).trans h0)

theorem IsSplit.add {C : Curve k} {D E : C.Div} (hD : IsSplit C D) (hE : IsSplit C E) :
    IsSplit C (D + E) := by
  intro Q hQ
  rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hQ
  have h : D Q ≠ 0 ∨ E Q ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hQ (by rw [hcon.1, hcon.2, add_zero])
  rcases h with h | h
  · exact hD Q (Finsupp.mem_support_iff.mpr h)
  · exact hE Q (Finsupp.mem_support_iff.mpr h)


end

end Curve

end Work.KeyLemma
