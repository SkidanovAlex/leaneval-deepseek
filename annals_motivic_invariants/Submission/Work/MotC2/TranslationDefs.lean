/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# Translation automorphisms of the function field of an elliptic curve: definitions

This file sets up the ingredients for the construction of the translation automorphisms
`Func E ≃ₐ[L] Func E` of the function field of an elliptic curve `E` over a field `L`:

* `transX E T`, `transY E T` are the coordinates of the sum of the generic point `(genX E, genY E)`
  of the base-changed curve with the point `T`;
* `pt E T` is the point `T` pushed forward to the function field;
* `genPoint E` is the generic point, `phiT E T` is the evaluation homomorphism
  `Coord E →ₐ[L] Func E` at `(transX E T, transY E T)`.
-/
import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

open Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace Work.MotC2

variable {L : Type*} [Field L]

/-! ## The Weierstrass relation for the generic point -/

lemma of_Y_coeff (E : WeierstrassCurve L) :
    AdjoinRoot.of (WeierstrassCurve.Affine.polynomial E) (C E.a₁ * X + C E.a₃) =
      algebraMap L (Coord E) E.a₁ * coordX E + algebraMap L (Coord E) E.a₃ := by
  rw [map_add, map_mul, of_poly_C, of_poly_C]
  rfl

lemma of_const_term (E : WeierstrassCurve L) :
    AdjoinRoot.of (WeierstrassCurve.Affine.polynomial E)
        (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) =
      (coordX E) ^ 3 + algebraMap L (Coord E) E.a₂ * (coordX E) ^ 2
        + algebraMap L (Coord E) E.a₄ * coordX E + algebraMap L (Coord E) E.a₆ := by
  rw [map_add, map_add, map_add, map_mul, map_mul, map_pow, map_pow, of_poly_C, of_poly_C, of_poly_C]
  rfl

/-- The Weierstrass relation in the coordinate ring `L[E]`. -/
lemma coord_relation (E : WeierstrassCurve L) :
    (coordY E) ^ 2 + (algebraMap L (Coord E) E.a₁ * coordX E + algebraMap L (Coord E) E.a₃)
        * coordY E =
      (coordX E) ^ 3 + algebraMap L (Coord E) E.a₂ * (coordX E) ^ 2
        + algebraMap L (Coord E) E.a₄ * coordX E + algebraMap L (Coord E) E.a₆ := by
  have h0 : Polynomial.eval₂ (AdjoinRoot.of (polynomial E)) (AdjoinRoot.root (polynomial E))
      (Y ^ 2 + C (C E.a₁ * X + C E.a₃) * Y - C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) =
      0 :=
    AdjoinRoot.eval₂_root _
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_C] at h0
  rw [of_Y_coeff E, of_const_term E] at h0
  dsimp only [coordY] at h0 ⊢
  linear_combination (norm := refl_ring1) h0

/-- The Weierstrass relation in the function field `L(E)`. -/
lemma genX_genY_relation (E : WeierstrassCurve L) :
    (genY E) ^ 2 + algebraMap L (Func E) E.a₁ * genX E * genY E
        + algebraMap L (Func E) E.a₃ * genY E =
      (genX E) ^ 3 + algebraMap L (Func E) E.a₂ * (genX E) ^ 2
        + algebraMap L (Func E) E.a₄ * genX E + algebraMap L (Func E) E.a₆ := by
  have h := congrArg (algebraMap (Coord E) (Func E)) (coord_relation E)
  simp only [map_add, map_mul, map_pow] at h
  rw [← genX, ← genY] at h
  linear_combination (norm := refl_ring1) h

/-- The generic point of the curve satisfies the Weierstrass equation. -/
lemma equation_genX_genY (E : WeierstrassCurve L) :
    Equation (baseE E) (genX E) (genY E) := by
  rw [equation_iff, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  exact genX_genY_relation E

/-! ## The generic point is not a constant -/

lemma algebraMap_LX_Coord_injective (E : WeierstrassCurve L) :
    Function.Injective (algebraMap (L[X]) (Coord E)) := by
  intro p q h
  have h0 : algebraMap (L[X]) (Coord E) (p - q) = 0 := by rw [map_sub, h, sub_self]
  have h1 : (p - q) • (1 : Coord E) = 0 := by
    rw [CoordinateRing.smul, mul_one, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq]
    exact h0
  have h2 := CoordinateRing.smul_basis_eq_zero (W' := E) (p := p - q) (q := 0) (by simpa using h1)
  exact sub_eq_zero.mp h2.1

lemma transcendental_genX (E : WeierstrassCurve L) : Transcendental L (genX E) := by
  rw [transcendental_iff_injective]
  have hcomp : (Polynomial.aeval (genX E) : L[X] →ₐ[L] Func E)
      = (IsScalarTower.toAlgHom L (Coord E) (Func E)).comp
          (IsScalarTower.toAlgHom L (L[X]) (Coord E)) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_X_eq_coordX,
      Polynomial.aeval_X, genX]
  rw [hcomp]
  exact fun p q h => algebraMap_LX_Coord_injective E (IsFractionRing.injective (Coord E) (Func E) h)

lemma genX_ne_algebraMap (E : WeierstrassCurve L) (c : L) :
    genX E ≠ algebraMap L (Func E) c := by
  intro h
  exact transcendental_genX E (h ▸ isAlgebraic_algebraMap c)

/-! ## The generic point and translation by a point -/

section Points

variable (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]

noncomputable local instance instDecEqFunc (E : WeierstrassCurve L) : DecidableEq (Func E) :=
  Classical.decEq _

/-- The `X`-coordinate of the sum of the generic point with the point `T`. -/
noncomputable def transX (T : E.toAffine.Point) : Func E :=
  match T with
  | .zero => genX E
  | .some a b _ =>
      addX (baseE E) (genX E) (algebraMap L (Func E) a)
        (slope (baseE E) (genX E) (algebraMap L (Func E) a) (genY E) (algebraMap L (Func E) b))

/-- The `Y`-coordinate of the sum of the generic point with the point `T`. -/
noncomputable def transY (T : E.toAffine.Point) : Func E :=
  match T with
  | .zero => genY E
  | .some a b _ =>
      addY (baseE E) (genX E) (algebraMap L (Func E) a) (genY E)
        (slope (baseE E) (genX E) (algebraMap L (Func E) a) (genY E) (algebraMap L (Func E) b))

@[simp]
lemma transX_zero : transX E Point.zero = genX E := rfl

@[simp]
lemma transY_zero : transY E Point.zero = genY E := rfl

lemma transX_some (a b : L) (h : Nonsingular E a b) :
    transX E (Point.some a b h) =
      addX (baseE E) (genX E) (algebraMap L (Func E) a)
        (slope (baseE E) (genX E) (algebraMap L (Func E) a) (genY E) (algebraMap L (Func E) b)) := rfl

lemma transY_some (a b : L) (h : Nonsingular E a b) :
    transY E (Point.some a b h) =
      addY (baseE E) (genX E) (algebraMap L (Func E) a) (genY E)
        (slope (baseE E) (genX E) (algebraMap L (Func E) a) (genY E) (algebraMap L (Func E) b)) := rfl

/-- The point `T` of `E` over `L`, viewed as a point over the function field `L(E)`. -/
noncomputable def pt (T : E.toAffine.Point) : (baseE E).toAffine.Point :=
  Point.map (W' := E.toAffine) (Algebra.ofId L (Func E)) T

@[simp]
lemma pt_zero : pt E (Point.zero : E.toAffine.Point) = 0 := map_zero _

lemma pt_add (P Q : E.toAffine.Point) : pt E (P + Q) = pt E P + pt E Q := map_add _ P Q

@[simp]
lemma pt_neg (T : E.toAffine.Point) : pt E (-T) = -pt E T := map_neg _ T

lemma pt_some_exists (a b : L) (h : Nonsingular E a b) :
    ∃ h' : Nonsingular (baseE E) (algebraMap L (Func E) a) (algebraMap L (Func E) b),
      pt E (Point.some a b h) =
        Point.some (algebraMap L (Func E) a) (algebraMap L (Func E) b) h' :=
  ⟨_, Point.map_some (W' := E.toAffine) (f := Algebra.ofId L (Func E)) (x := a) (y := b) h⟩

noncomputable def ptNonsingular (a b : L) (h : Nonsingular E a b) :
    Nonsingular (baseE E) (algebraMap L (Func E) a) (algebraMap L (Func E) b) :=
  (pt_some_exists E a b h).choose

lemma pt_some (a b : L) (h : Nonsingular E a b) :
    pt E (Point.some a b h) =
      Point.some (algebraMap L (Func E) a) (algebraMap L (Func E) b) (ptNonsingular E a b h) :=
  (pt_some_exists E a b h).choose_spec

noncomputable def genNonsingular : Nonsingular (baseE E) (genX E) (genY E) :=
  equation_iff_nonsingular.mp (equation_genX_genY E)

/-- The generic point `(genX E, genY E)` of the base-changed curve. -/
noncomputable def genPoint : (baseE E).toAffine.Point :=
  Point.some (genX E) (genY E) (genNonsingular E)

@[simp]
lemma genPoint_def : genPoint E = Point.some (genX E) (genY E) (genNonsingular E) := rfl

/-- The `Nonsingular` proof for the coordinates of the generic translated point. -/
noncomputable def transNonsingular : (T : E.toAffine.Point) →
    Nonsingular (baseE E) (transX E T) (transY E T)
  | .zero => genNonsingular E
  | .some a b h =>
      nonsingular_add (genNonsingular E) (ptNonsingular E a b h)
        (fun hxy => genX_ne_algebraMap E a hxy.1)

lemma genPoint_add_pt (T : E.toAffine.Point) :
    genPoint E + pt E T = Point.some (transX E T) (transY E T) (transNonsingular E T) := by
  cases T with
  | zero =>
      simp only [genPoint_def, pt_zero, add_zero, transX_zero, transY_zero, transNonsingular]
  | some a b h =>
      rw [pt_some, genPoint_def, Point.add_of_X_ne (genX_ne_algebraMap E a)]
      rfl

lemma equation_transX_transY (T : E.toAffine.Point) :
    Equation (baseE E) (transX E T) (transY E T) :=
  (transNonsingular E T).1

/-! ### Nondegeneracy: the generic point is not a constant point -/

lemma genPoint_ne_pt (T : E.toAffine.Point) : genPoint E ≠ pt E T := by
  cases T with
  | zero =>
      rw [pt_zero]
      exact Point.some_ne_zero _
  | some a b h =>
      rw [pt_some]
      intro hh
      rw [genPoint_def, Point.some.injEq] at hh
      exact genX_ne_algebraMap E a hh.1

lemma genPoint_add_pt_ne_pt (T S : E.toAffine.Point) : genPoint E + pt E T ≠ pt E S := by
  intro h
  have h1 : pt E S - pt E T = pt E (S - T) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← pt_neg E T, ← pt_add]
  have h2 : genPoint E = pt E S - pt E T := (eq_sub_iff_add_eq).mpr h
  rw [h1] at h2
  exact genPoint_ne_pt E (S - T) h2

lemma genPoint_add_pt_ne_neg_pt (T S : E.toAffine.Point) : genPoint E + pt E T ≠ -pt E S := by
  intro h
  have h1 : pt E (-S) - pt E T = pt E (-S - T) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← pt_neg E T, ← pt_add]
  have h2 : genPoint E = pt E (-S) - pt E T := (eq_sub_iff_add_eq).mpr (by rw [h, pt_neg])
  rw [h1] at h2
  exact genPoint_ne_pt E (-S - T) h2

/-- The `X`-coordinate of the generic translated point is never the `X`-coordinate of a
rational point. -/
lemma transX_ne_algebraMap (T : E.toAffine.Point) (c d : L) (h : Nonsingular E c d) :
    transX E T ≠ algebraMap L (Func E) c := by
  intro hc
  have hdisj := (Point.X_eq_iff (h₁ := transNonsingular E T)
    (h₂ := ptNonsingular E c d h)).mp hc
  rw [← genPoint_add_pt E T, ← pt_some E c d h] at hdisj
  rcases hdisj with h' | h'
  · exact genPoint_add_pt_ne_pt E T (Point.some c d h) h'
  · exact genPoint_add_pt_ne_neg_pt E T (Point.some c d h) h'

/-! ### The round trip: subtracting `T` again -/

/-- The slope of the line through the translated generic point and the point `-T`. -/
noncomputable def negSlope {a b : L} (h : Nonsingular E a b) : Func E :=
  WeierstrassCurve.Affine.slope (baseE E) (transX E (Point.some a b h))
    (algebraMap L (Func E) a) (transY E (Point.some a b h))
    (WeierstrassCurve.Affine.negY (baseE E) (algebraMap L (Func E) a) (algebraMap L (Func E) b))

/-- Adding `T` to the generic point and then subtracting it again returns the generic point:
the coordinates of `(genX E, genY E)` are obtained from those of the translated point by the
addition formulae with the slope of the line through `(transX E T, transY E T)` and `-T`. -/
lemma genPoint_round_trip {a b : L} (h : Nonsingular E a b) :
    genX E = addX (baseE E) (transX E (Point.some a b h)) (algebraMap L (Func E) a)
        (negSlope E h) ∧
      genY E = addY (baseE E) (transX E (Point.some a b h)) (algebraMap L (Func E) a)
        (transY E (Point.some a b h)) (negSlope E h) := by
  have hne : transX E (Point.some a b h) ≠ algebraMap L (Func E) a :=
    transX_ne_algebraMap E _ a b h
  have hgrp : (genPoint E + pt E (Point.some a b h)) + (- pt E (Point.some a b h)) =
      genPoint E := by
    abel
  rw [genPoint_add_pt E (Point.some a b h), pt_some, Point.neg_some,
    Point.add_of_X_ne hne, genPoint_def] at hgrp
  rw [Point.some.injEq] at hgrp
  exact ⟨hgrp.1.symm, hgrp.2.symm⟩

/-- The slope of the round trip is the quotient `(transY - negY a b) / (transX - a)`. -/
lemma negSlope_eq {a b : L} (h : Nonsingular E a b) :
    negSlope E h =
      (transY E (Point.some a b h) -
        WeierstrassCurve.Affine.negY (baseE E) (algebraMap L (Func E) a)
          (algebraMap L (Func E) b)) /
      (transX E (Point.some a b h) - algebraMap L (Func E) a) := by
  rw [negSlope, slope_of_X_ne]
  exact transX_ne_algebraMap E _ a b h


/-! ## Algebraicity and transcendence of the translated generic point -/

section Algebraicity

open scoped IntermediateField

/-- Elementwise transitivity of algebraicity along a simple extension: if `x` is algebraic over
the field generated by an algebraic element `U`, then `x` is algebraic over the base field. -/
lemma isAlgebraic_of_isAlgebraic_adjoin_simple {L : Type*} [Field L] {F : Type*} [Field F]
    [Algebra L F] {U x : F} (hU : IsAlgebraic L U)
    (hx : IsAlgebraic ↥(L⟮U⟯) x) : IsAlgebraic L x := by
  haveI h1 : Algebra.IsAlgebraic L ↥(L⟮U⟯) :=
    IntermediateField.isAlgebraic_adjoin_simple hU.isIntegral
  haveI h2 : Algebra.IsAlgebraic ↥(L⟮U⟯) ↥((↥(L⟮U⟯))⟮x⟯) :=
    IntermediateField.isAlgebraic_adjoin_simple hx.isIntegral
  have h3 : Algebra.IsAlgebraic L ↥((↥(L⟮U⟯))⟮x⟯) :=
    Algebra.IsAlgebraic.trans (R := L) (S := ↥(L⟮U⟯)) (A := ↥((↥(L⟮U⟯))⟮x⟯))
  have hmem : x ∈ (↥(L⟮U⟯))⟮x⟯ := IntermediateField.mem_adjoin_simple_self (↥(L⟮U⟯)) x
  have h3' : Algebra.IsAlgebraic L ↥(((↥(L⟮U⟯))⟮x⟯).restrictScalars L) := h3
  have h5 : IsAlgebraic L (⟨x, hmem⟩ : ↥(((↥(L⟮U⟯))⟮x⟯).restrictScalars L)) :=
    Algebra.IsAlgebraic.isAlgebraic (R := L)
      (A := ↥(((↥(L⟮U⟯))⟮x⟯).restrictScalars L)) ⟨x, hmem⟩
  exact (IntermediateField.isAlgebraic_iff (S := ((↥(L⟮U⟯))⟮x⟯).restrictScalars L)).mp h5

/-- If `(U, V)` satisfies the Weierstrass equation, then `V` is algebraic over the field
generated by `U`. -/
lemma isAlgebraic_of_equation {U V : Func E} (h : Equation (baseE E) U V) :
    IsAlgebraic ↥(L⟮U⟯) V := by
  rw [equation_iff, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  have hmemU : U ∈ L⟮U⟯ := IntermediateField.mem_adjoin_simple_self L U
  have hc : (algebraMap L (Func E) E.a₁ * U + algebraMap L (Func E) E.a₃) ∈ L⟮U⟯ :=
    add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hmemU)
      (IntermediateField.algebraMap_mem _ _)
  have hf : (U ^ 3 + algebraMap L (Func E) E.a₂ * U ^ 2 + algebraMap L (Func E) E.a₄ * U
      + algebraMap L (Func E) E.a₆) ∈ L⟮U⟯ := by
    refine add_mem (add_mem (add_mem (pow_mem hmemU 3) ?_) ?_)
      (IntermediateField.algebraMap_mem _ _)
    · exact mul_mem (IntermediateField.algebraMap_mem _ _) (pow_mem hmemU 2)
    · exact mul_mem (IntermediateField.algebraMap_mem _ _) hmemU
  refine ⟨Polynomial.X ^ 2 + Polynomial.C ⟨_, hc⟩ * Polynomial.X - Polynomial.C ⟨_, hf⟩,
    ?_, ?_⟩
  · intro hp
    have h2 : (Polynomial.X ^ 2 + Polynomial.C (⟨_, hc⟩ : ↥(L⟮U⟯)) * Polynomial.X
        - Polynomial.C (⟨_, hf⟩ : ↥(L⟮U⟯)) : (↥(L⟮U⟯))[X]).coeff 2 = 1 := by
      simp
    rw [hp] at h2
    simp at h2
  · have hmain : Polynomial.aeval V (Polynomial.X ^ 2 + Polynomial.C (⟨_, hc⟩ : ↥(L⟮U⟯))
          * Polynomial.X - Polynomial.C (⟨_, hf⟩ : ↥(L⟮U⟯)) : (↥(L⟮U⟯))[X])
        = V ^ 2 + (algebraMap L (Func E) E.a₁ * U + algebraMap L (Func E) E.a₃) * V
          - (U ^ 3 + algebraMap L (Func E) E.a₂ * U ^ 2 + algebraMap L (Func E) E.a₄ * U
            + algebraMap L (Func E) E.a₆) := by
      simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      rfl
    rw [hmain]
    linear_combination (norm := refl_ring1) h

/-- The `Y`-coordinate of the translated generic point is algebraic over `L` as soon as the
`X`-coordinate is. -/
lemma isAlgebraic_transY_of_transX {a b : L} (h : Nonsingular E a b)
    (hU : IsAlgebraic L (transX E (Point.some a b h))) :
    IsAlgebraic L (transY E (Point.some a b h)) :=
  isAlgebraic_of_isAlgebraic_adjoin_simple hU
    (isAlgebraic_of_equation E (transNonsingular E (Point.some a b h)).1)

/-- The `X`-coordinate of the sum of the generic point with an affine point. -/
noncomputable def tU {a b : L} (h : Nonsingular E a b) : Func E :=
  transX E (Point.some a b h)

/-- The `Y`-coordinate of the sum of the generic point with an affine point. -/
noncomputable def tV {a b : L} (h : Nonsingular E a b) : Func E :=
  transY E (Point.some a b h)

lemma tU_def {a b : L} (h : Nonsingular E a b) : tU E h = transX E (Point.some a b h) := rfl

lemma tV_def {a b : L} (h : Nonsingular E a b) : tV E h = transY E (Point.some a b h) := rfl

/-- The slope of the line through the translated generic point and the point `-T` lies in the
field generated by the translated coordinates. -/
lemma negSlope_mem {a b : L} (h : Nonsingular E a b) :
    negSlope E h ∈ (L⟮tU E h⟯)⟮tV E h⟯ := by
  have hconst : ∀ c : L, algebraMap L (Func E) c ∈ (L⟮tU E h⟯)⟮tV E h⟯ := by
    intro c
    have h' := IntermediateField.algebraMap_mem ((L⟮tU E h⟯)⟮tV E h⟯)
      (algebraMap L (↥(L⟮tU E h⟯)) c)
    rw [← IsScalarTower.algebraMap_apply L (↥(L⟮tU E h⟯)) (Func E) c] at h'
    exact h'
  have hmemU : tU E h ∈ (L⟮tU E h⟯)⟮tV E h⟯ := by
    have h' := IntermediateField.adjoin.range_algebraMap_subset (F := L⟮tU E h⟯)
      (S := ({tV E h} : Set (Func E)))
      (Set.mem_range_self (⟨tU E h, IntermediateField.mem_adjoin_simple_self L (tU E h)⟩ :
        L⟮tU E h⟯))
    simpa using h'
  have hmemV : tV E h ∈ (L⟮tU E h⟯)⟮tV E h⟯ :=
    IntermediateField.mem_adjoin_simple_self (L⟮tU E h⟯) (tV E h)
  rw [negSlope, slope_of_X_ne (transX_ne_algebraMap E _ a b h)]
  refine div_mem (sub_mem hmemV ?_) (sub_mem hmemU (hconst a))
  rw [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  exact sub_mem (sub_mem (neg_mem (hconst b)) (mul_mem (hconst E.a₁) (hconst a)))
    (hconst E.a₃)

/-- The generic point lies in the field generated by the translated coordinates. -/
lemma genX_mem_adjoin {a b : L} (h : Nonsingular E a b) :
    genX E ∈ (L⟮tU E h⟯)⟮tV E h⟯ := by
  have hconst : ∀ c : L, algebraMap L (Func E) c ∈ (L⟮tU E h⟯)⟮tV E h⟯ := by
    intro c
    have h' := IntermediateField.algebraMap_mem ((L⟮tU E h⟯)⟮tV E h⟯)
      (algebraMap L (↥(L⟮tU E h⟯)) c)
    rw [← IsScalarTower.algebraMap_apply L (↥(L⟮tU E h⟯)) (Func E) c] at h'
    exact h'
  have hmemU : tU E h ∈ (L⟮tU E h⟯)⟮tV E h⟯ := by
    have h' := IntermediateField.adjoin.range_algebraMap_subset (F := L⟮tU E h⟯)
      (S := ({tV E h} : Set (Func E)))
      (Set.mem_range_self (⟨tU E h, IntermediateField.mem_adjoin_simple_self L (tU E h)⟩ :
        L⟮tU E h⟯))
    simpa using h'
  have hs := negSlope_mem E h
  rw [(genPoint_round_trip E h).1, WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂]
  exact sub_mem (sub_mem (sub_mem (add_mem (pow_mem hs 2) (mul_mem (hconst E.a₁) hs))
    (hconst E.a₂)) hmemU) (hconst a)

/-- The `X`-coordinate of the translated generic point is transcendental over `L`. -/
lemma transcendental_transX (T : E.toAffine.Point) : Transcendental L (transX E T) := by
  cases T with
  | zero => rw [transX_zero]; exact transcendental_genX E
  | some a b h =>
      intro hU
      have hV : IsAlgebraic L (tV E h) := isAlgebraic_transY_of_transX E h hU
      have hmemX : genX E ∈ (L⟮tU E h⟯)⟮tV E h⟯ := genX_mem_adjoin E h
      have hmemX2 : genX E ∈ L⟮tU E h, tV E h⟯ := by
        have hh : genX E ∈ (L⟮tU E h⟯)⟮tV E h⟯.restrictScalars L := hmemX
        rwa [IntermediateField.adjoin_simple_adjoin_simple (F := L) (tU E h) (tV E h)] at hh
      haveI : Algebra.IsAlgebraic L ↥(L⟮tU E h, tV E h⟯) :=
        IntermediateField.isAlgebraic_adjoin (K := L) (L := Func E)
          (S := ({tU E h, tV E h} : Set (Func E))) (fun y hy => by
            rcases hy with rfl | rfl
            · simpa only [tU_def] using hU.isIntegral
            · simpa only [tV_def] using hV.isIntegral)
      have h5 : IsAlgebraic L (⟨genX E, hmemX2⟩ : ↥(L⟮tU E h, tV E h⟯)) :=
        Algebra.IsAlgebraic.isAlgebraic (R := L) (A := ↥(L⟮tU E h, tV E h⟯))
          ⟨genX E, hmemX2⟩
      exact transcendental_genX E ((IntermediateField.isAlgebraic_iff (S := L⟮tU E h, tV E h⟯)).mp h5)

end Algebraicity

end Points

end Work.MotC2
