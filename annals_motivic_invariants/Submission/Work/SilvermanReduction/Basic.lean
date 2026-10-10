/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Mathlib
import ChallengeDeps

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The reduction map on the points of a Weierstrass curve at a discrete valuation

This is the interface of the area `Submission/Work/SilvermanReduction`: Silverman, *AEC*,
VII.2.1–2.2 — the reduction of the **points** of a Weierstrass curve over a discretely valued
field, the missing theorem of the paper's `lem:torsors` for the number-field class (a).

The setting throughout is a discrete valuation ring `R` with fraction field `K = Frac R`, and a
Weierstrass curve `W/K` with **good reduction** at the place: `W` is integral over `R` and the
reduction `W.reduction R` of a minimal model is an elliptic curve over the residue field.

## Main definitions

* `val R K` — the `ℤᵐ⁰`-valued valuation of `K = Frac R` at the maximal ideal of `R`.
* `IsIntegralK R K x` — `x` is integral: `val R K x ≤ 1`.
* `redPoint R W` — the reduction map on points `E(K) → Ẽ(k)`.
* `E1 R W` — the set of points of negative valuation (the kernel of `redPoint`).
* `ReducesIdentity R K σ` — `σ` acts trivially on the residue field.

## Main results (the Silverman VII.2.1–2.2 chapter)

* `IsIntegralK.iff_exists` — integrality is "lifts to `R`".
* `isIntegralK_of_equation` — for a point of an integral Weierstrass equation, the `x`-coordinate
  is integral if and only if the `y`-coordinate is.
* `redPoint_zero`, `redPoint_some`, `redPoint_eq_zero_iff` — the elementary theory.
* `redPoint_add` — **Silverman VII.2.1**: `redPoint` is additive.
* `map_redPoint` — **the Galois compatibility**: a `σ` acting trivially on the residue field
  commutes with `redPoint`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## 1. Integrality -/

/-- The `ℤᵐ⁰`-valued valuation of `K = Frac R` at the maximal ideal of `R`. -/
noncomputable def val : Valuation K ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal R).valuation K

variable {R K}

lemma val_algebraMap (r : R) : val R K (algebraMap R K r) ≤ 1 := by
  rw [val]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (IsDiscreteValuationRing.maximalIdeal R) r

lemma val_algebraMap_lt_one_iff {r : R} :
    val R K (algebraMap R K r) < 1 ↔ r ∈ IsLocalRing.maximalIdeal R := by
  rw [val]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
    (IsDiscreteValuationRing.maximalIdeal R) r

lemma val_algebraMap_eq_one_iff {r : R} :
    val R K (algebraMap R K r) = 1 ↔ r ∉ IsLocalRing.maximalIdeal R := by
  rw [val]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
    (v := IsDiscreteValuationRing.maximalIdeal R)

lemma algebraMap_injective : Function.Injective (algebraMap R K) :=
  IsFractionRing.injective R K

/-- **Integrality at the place.**  `x : K` is integral if `val R K x ≤ 1`. -/
def IsIntegralK (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (x : K) : Prop :=
  val R K x ≤ 1

namespace IsIntegralK

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem of_algebraMap (r : R) : IsIntegralK R K (algebraMap R K r) :=
  val_algebraMap r

theorem iff_exists (x : K) : IsIntegralK R K x ↔ ∃ r : R, algebraMap R K r = x := by
  constructor
  · intro h
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := R) (K := K) h
  · rintro ⟨r, rfl⟩
    exact of_algebraMap r

theorem iff_exists_mem (x : K) :
    val R K x < 1 ↔ ∃ r ∈ IsLocalRing.maximalIdeal R, algebraMap R K r = x := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := (iff_exists x).mp h.le
    rw [← hr] at h
    rw [val_algebraMap_lt_one_iff] at h
    exact ⟨r, h, hr⟩
  · rintro ⟨r, hr, rfl⟩
    rwa [val_algebraMap_lt_one_iff]

theorem add {x y : K} (hx : IsIntegralK R K x) (hy : IsIntegralK R K y) :
    IsIntegralK R K (x + y) :=
  show val R K (x + y) ≤ 1 from
    Valuation.map_add_le (val R K) (show val R K x ≤ 1 from hx) (show val R K y ≤ 1 from hy)

theorem mul {x y : K} (hx : IsIntegralK R K x) (hy : IsIntegralK R K y) :
    IsIntegralK R K (x * y) := by
  show val R K (x * y) ≤ 1
  rw [map_mul]
  simpa using mul_le_mul' (show val R K x ≤ 1 from hx) (show val R K y ≤ 1 from hy)

theorem pow {x : K} (hx : IsIntegralK R K x) (n : ℕ) : IsIntegralK R K (x ^ n) := by
  induction n with
  | zero => simpa using (of_algebraMap (R := R) (K := K) (1 : R))
  | succ n ih => rw [pow_succ]; exact ih.mul hx

theorem neg {x : K} (hx : IsIntegralK R K x) : IsIntegralK R K (-x) := by
  simpa [IsIntegralK] using hx

theorem sub {x y : K} (hx : IsIntegralK R K x) (hy : IsIntegralK R K y) :
    IsIntegralK R K (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

end IsIntegralK

/-! ## 2. The equation of a Weierstrass curve under a ring homomorphism -/

section EquationMap

variable {R S : Type*} [CommRing R] [CommRing S] {W : Affine R}

/-- The Weierstrass equation is preserved by any ring homomorphism (no injectivity needed). -/
lemma equation_map (f : R →+* S) {x y : R} (h : Equation W x y) :
    Equation (W.map f) (f x) (f y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  simpa only [map_add, map_mul, map_pow] using congrArg f h

end EquationMap

/-! ## 3. Integrality of the coefficients and of the `y`-coordinate -/

section Integral

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]
variable {W : Affine K} [W.IsIntegral R]

lemma isIntegralK_a₁ : IsIntegralK R K W.a₁ := by
  obtain ⟨I, hI⟩ := WeierstrassCurve.IsIntegral.integral (R := R) (W := W)
  rw [hI]
  simpa using IsIntegralK.of_algebraMap (R := R) (K := K) I.a₁

lemma isIntegralK_a₂ : IsIntegralK R K W.a₂ := by
  obtain ⟨I, hI⟩ := WeierstrassCurve.IsIntegral.integral (R := R) (W := W)
  rw [hI]
  simpa using IsIntegralK.of_algebraMap (R := R) (K := K) I.a₂

lemma isIntegralK_a₃ : IsIntegralK R K W.a₃ := by
  obtain ⟨I, hI⟩ := WeierstrassCurve.IsIntegral.integral (R := R) (W := W)
  rw [hI]
  simpa using IsIntegralK.of_algebraMap (R := R) (K := K) I.a₃

lemma isIntegralK_a₄ : IsIntegralK R K W.a₄ := by
  obtain ⟨I, hI⟩ := WeierstrassCurve.IsIntegral.integral (R := R) (W := W)
  rw [hI]
  simpa using IsIntegralK.of_algebraMap (R := R) (K := K) I.a₄

lemma isIntegralK_a₆ : IsIntegralK R K W.a₆ := by
  obtain ⟨I, hI⟩ := WeierstrassCurve.IsIntegral.integral (R := R) (W := W)
  rw [hI]
  simpa using IsIntegralK.of_algebraMap (R := R) (K := K) I.a₆

/-- **For an integral Weierstrass equation, `x`-integrality implies `y`-integrality.** -/
theorem isIntegralK_of_equation {x y : K} (heq : Equation W x y) (hx : IsIntegralK R K x) :
    IsIntegralK R K y := by
  by_contra hcon
  rw [IsIntegralK, not_le] at hcon
  have hrhs : val R K (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) ≤ 1 :=
    (((hx.pow 3).add (isIntegralK_a₂.mul (hx.pow 2))).add (isIntegralK_a₄.mul hx)).add
      isIntegralK_a₆
  have hmid : val R K (W.a₁ * x + W.a₃) ≤ 1 :=
    (isIntegralK_a₁.mul hx).add isIntegralK_a₃
  have hsum : val R K (y + (W.a₁ * x + W.a₃)) = val R K y := by
    rw [add_comm]
    exact Valuation.map_add_eq_of_lt_right _ (lt_of_le_of_lt hmid hcon)
  have hlhs : val R K (y ^ 2 + W.a₁ * x * y + W.a₃ * y) = val R K y * val R K y := by
    have h0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y * (y + (W.a₁ * x + W.a₃)) := by ring
    rw [h0, map_mul, hsum]
  have heq' : val R K (y ^ 2 + W.a₁ * x * y + W.a₃ * y)
      = val R K (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    rw [← heq]
  have hgt : 1 < val R K y * val R K y := one_lt_mul_of_lt_of_le hcon hcon.le
  rw [← hlhs, heq'] at hgt
  exact absurd (lt_of_lt_of_le hgt hrhs) (lt_irrefl (1 : ℤᵐ⁰))

/-- An integral `x`-coordinate has an integral `y`-coordinate. -/
lemma exists_lift_of_y {x y : K} (h : Nonsingular W x y)
    (hx : ∃ r : R, algebraMap R K r = x) : ∃ s : R, algebraMap R K s = y :=
  (IsIntegralK.iff_exists y).mp
    (isIntegralK_of_equation h.1 ((IsIntegralK.iff_exists x).mpr hx))

end Integral

/-! ## 4. The reduced curve and the reduction of points -/

section Reduction

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]

/-- Good reduction makes the special fibre an elliptic curve. -/
lemma isElliptic_reduction {W : Affine K} [W.HasGoodReduction R] :
    (W.reduction R).IsElliptic :=
  (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance

attribute [instance] isElliptic_reduction

/-- The equation of the integral model holds at lifts of an equation point. -/
lemma equation_integralModel {W : Affine K} [W.IsIntegral R] {x y : K}
    (h : Equation W x y) {r s : R} (hr : algebraMap R K r = x) (hs : algebraMap R K s = y) :
    Equation (WeierstrassCurve.integralModel R W) r s := by
  have h1 : (WeierstrassCurve.integralModel R W)⁄K = W :=
    WeierstrassCurve.baseChange_integralModel_eq R W
  have h2 : Equation ((WeierstrassCurve.integralModel R W)⁄K) (algebraMap R K r)
      (algebraMap R K s) := by
    rw [h1, hr, hs]; exact h
  exact (WeierstrassCurve.Affine.map_equation (W := WeierstrassCurve.integralModel R W)
    (f := algebraMap R K) (algebraMap_injective) r s).mp h2

/-- A nonsingular point of the integral model reduces to a nonsingular point of the special
fibre, when the reduction is elliptic. -/
lemma nonsingular_reduction {W : Affine K} [W.HasGoodReduction R] {r s : R}
    (h : Equation (WeierstrassCurve.integralModel R W) r s) :
    Nonsingular (W.reduction R) (residue R r) (residue R s) := by
  have h' : Equation (W.reduction R) (residue R r) (residue R s) := by
    have := equation_map (W := WeierstrassCurve.integralModel R W) (residue R) h
    simpa only [WeierstrassCurve.reduction] using this
  exact (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W.reduction R)).mp h'

/-- **The reduction map on the points of a Weierstrass curve at a place of good reduction.**
An integral point reduces coordinatewise to the special fibre; a point of negative valuation
reduces to `0`. -/
noncomputable def redPoint (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : Affine K) [hW : W.HasGoodReduction R] :
    WeierstrassCurve.Affine.Point W → WeierstrassCurve.Affine.Point (W.reduction R) := by
  classical
  letI : (W.reduction R).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction R).mp hW
  refine fun P => match P with
    | WeierstrassCurve.Affine.Point.zero => 0
    | WeierstrassCurve.Affine.Point.some x y h =>
      if hx : ∃ r : R, algebraMap R K r = x then
        WeierstrassCurve.Affine.Point.some (residue R hx.choose)
          (residue R (exists_lift_of_y (W := W) h hx).choose)
          (nonsingular_reduction (W := W)
            (equation_integralModel (W := W) h.1 hx.choose_spec
              (exists_lift_of_y (W := W) h hx).choose_spec))
      else 0

/-! ## 5. The API of the reduction map -/

/-- Two lifts of the same integral element have the same residue. -/
lemma residue_eq_of_algebraMap_eq {r s : R} (h : algebraMap R K r = algebraMap R K s) :
    residue R r = residue R s := by
  have h0 : algebraMap R K (r - s) = 0 := by rw [RingHom.map_sub, h, sub_self]
  have h1 : r - s = 0 := algebraMap_injective (h0.trans (map_zero (algebraMap R K)).symm)
  rw [sub_eq_zero] at h1
  rw [h1]

/-- Any lift of an integral element has the residue of the chosen lift. -/
lemma residue_of_lift {x : K} (hx : ∃ r : R, algebraMap R K r = x) {r : R}
    (hr : algebraMap R K r = x) : residue R r = residue R hx.choose :=
  residue_eq_of_algebraMap_eq (by rw [hr, hx.choose_spec])

/-- `P` has negative valuation: it is a nonzero point whose `x`-coordinate does not lift to `R`. -/
def HasNegativeValuation (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {W : Affine K} (P : WeierstrassCurve.Affine.Point W) : Prop :=
  ∃ (x y : K) (h : Nonsingular W x y),
    P = WeierstrassCurve.Affine.Point.some x y h ∧ ¬ ∃ r : R, algebraMap R K r = x

/-- **The subgroup `E₁(K)` of points of negative valuation.** -/
def E1 (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : Affine K) : Set (WeierstrassCurve.Affine.Point W) :=
  {P | HasNegativeValuation R P}

-- Note.  There is no separate definition of `E₀(K)` here: in the *good reduction* case the special
-- fibre `Ẽ` is smooth, so every point of `E(K)` reduces to a nonsingular point of `Ẽ` and
-- `E₀(K) = E(K)`.  (The points whose `x`-coordinate is integral — the "integral points" — are *not*
-- a subgroup of `E(K)`: they form the complement of `E₁(K)`, i.e. a union of cosets.  Silverman's
-- `E₀` is the preimage of the smooth part of the special fibre, which here is everything.)

section RedAPI

variable {K : Type*} [Field K]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]
variable {W : Affine K} [W.HasGoodReduction R]

lemma redPoint_zero : redPoint R W (0 : WeierstrassCurve.Affine.Point W) = 0 := rfl

lemma not_hasNegativeValuation_zero : ¬ HasNegativeValuation R (0 : WeierstrassCurve.Affine.Point W) := by
  rintro ⟨x, y, h, hP, -⟩
  exact WeierstrassCurve.Affine.Point.some_ne_zero h hP.symm

lemma hasNegativeValuation_some_iff {x y : K} (h : Nonsingular W x y) :
    HasNegativeValuation R (WeierstrassCurve.Affine.Point.some x y h) ↔ 1 < val R K x := by
  rw [HasNegativeValuation]
  constructor
  · rintro ⟨x', y', h', hP, hx'⟩
    rw [WeierstrassCurve.Affine.Point.some.injEq] at hP
    have hnot : ¬ IsIntegralK R K x' :=
      fun hI => hx' ((IsIntegralK.iff_exists (R := R) x').mp hI)
    rw [hP.1]
    exact not_le.mp hnot
  · intro hlt
    refine ⟨x, y, h, rfl, ?_⟩
    exact (IsIntegralK.iff_exists (R := R) x).not.mp (not_le.mpr hlt)

lemma not_hasNegativeValuation_some_iff {x y : K} (h : Nonsingular W x y) :
    ¬ HasNegativeValuation R (WeierstrassCurve.Affine.Point.some x y h) ↔
      ∃ r : R, algebraMap R K r = x := by
  rw [hasNegativeValuation_some_iff R h, not_lt]
  exact IsIntegralK.iff_exists (R := R) x

/-- Two `Point.some`'s with the same coordinates are equal (the nonsingularity proofs are
irrelevant). -/
theorem Point.some_congr {x y : K} (h h' : Nonsingular W x y) :
    (WeierstrassCurve.Affine.Point.some x y h : WeierstrassCurve.Affine.Point W) =
      WeierstrassCurve.Affine.Point.some x y h' := by
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

/-- **The reduction of an integral point, in terms of any lifts of its coordinates.** -/
theorem redPoint_some_mk {x y : K} (h : Nonsingular W x y) {r s : R}
    (hr : algebraMap R K r = x) (hs : algebraMap R K s = y) :
    redPoint R W (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some (residue R r) (residue R s)
        (nonsingular_reduction (W := W) (equation_integralModel (W := W) h.1 hr hs)) := by
  classical
  have hx : ∃ r : R, algebraMap R K r = x := ⟨r, hr⟩
  have hy : ∃ s : R, algebraMap R K s = y := ⟨s, hs⟩
  rw [redPoint, dite_eq_left hx]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨(residue_of_lift hx hr).symm, (residue_of_lift hy hs).symm⟩

/-- The reduction of a point of negative valuation is `0`. -/
theorem redPoint_some_eq_zero {x y : K} (h : Nonsingular W x y)
    (hx : ¬ ∃ r : R, algebraMap R K r = x) :
    redPoint R W (WeierstrassCurve.Affine.Point.some x y h) = 0 := by
  classical
  rw [redPoint, dite_eq_right hx]

/-- **The kernel of the reduction map.**  A point reduces to `0` exactly when it is the origin or
has negative valuation. -/
theorem redPoint_eq_zero_iff (P : WeierstrassCurve.Affine.Point W) :
    redPoint R W P = 0 ↔ P = 0 ∨ HasNegativeValuation R P := by
  classical
  rcases P with _ | ⟨x, y, h⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def, redPoint_zero]
    exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  · by_cases hx : ∃ r : R, algebraMap R K r = x
    · have hxI : IsIntegralK R K x := (IsIntegralK.iff_exists (R := R) x).mpr hx
      rw [redPoint_some_mk (R := R) h hx.choose_spec
          (exists_lift_of_y (W := W) h hx).choose_spec,
        hasNegativeValuation_some_iff R h]
      refine ⟨fun h0 => absurd h0 (WeierstrassCurve.Affine.Point.some_ne_zero _), fun h0 => ?_⟩
      rcases h0 with h0 | h0
      · exact absurd h0 (WeierstrassCurve.Affine.Point.some_ne_zero h)
      · exact absurd h0 (not_lt.mpr hxI)
    · rw [redPoint_some_eq_zero (R := R) h hx, hasNegativeValuation_some_iff R h]
      refine ⟨fun _ => Or.inr ?_, fun _ => rfl⟩
      exact not_le.mp (fun hI => hx ((IsIntegralK.iff_exists (R := R) x).mp hI))

/-- The points of negative valuation are exactly the nonzero points reducing to `0`. -/
theorem E1_eq_kernel (P : WeierstrassCurve.Affine.Point W) :
    P ∈ E1 R W ↔ P ≠ 0 ∧ redPoint R W P = 0 := by
  rw [E1, Set.mem_setOf_eq, redPoint_eq_zero_iff R P]
  constructor
  · intro h
    exact ⟨fun h0 => not_hasNegativeValuation_zero R (h0 ▸ h), Or.inr h⟩
  · rintro ⟨h0, h | h⟩
    · exact absurd h h0
    · exact h

/-- The reduction of a nonzero integral point is non-zero. -/
theorem redPoint_ne_zero_of_not_negativeVal (P : WeierstrassCurve.Affine.Point W)
    (hP : ¬ HasNegativeValuation R P) (h0 : P ≠ 0) : redPoint R W P ≠ 0 := by
  intro h
  rcases (redPoint_eq_zero_iff R P).mp h with h' | h'
  · exact h0 h'
  · exact hP h'

end RedAPI

end Reduction

/-! ## 6. Compatibility of the reduction with an automorphism of the valued field -/

section Galois

variable {K : Type*} [Field K]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]

/-- `σ` preserves the valuation of the place.  This holds for every automorphism of `K` when the
place is the *unique* extension of the valuation of the prime field, e.g. for a totally ramified
place of a number field. -/
def PreservesValuation (σ : K →+* K) : Prop :=
  ∀ x : K, val R K (σ x) = val R K x

/-- `σ` acts trivially on the residue field of the place. -/
def TrivialOnResidue (σ : K →+* K) : Prop :=
  ∀ x : K, IsIntegralK R K x → val R K (σ x - x) < 1

/-- If `σ` acts trivially on the residue field, then the reduction of an integral element is the
same whether one reduces it or its image under `σ`. -/
lemma residue_eq_of_trivialOnResidue {σ : K →+* K} (hτ : TrivialOnResidue R σ) {x : K}
    (hx : IsIntegralK R K x) {r r' : R} (hr : algebraMap R K r = x)
    (hr' : algebraMap R K r' = σ x) : residue R r' = residue R r := by
  have h : val R K (algebraMap R K (r' - r)) < 1 := by
    rw [map_sub, hr', hr]
    exact hτ x hx
  rw [val_algebraMap_lt_one_iff] at h
  have hz : residue R (r' - r) = 0 := (IsLocalRing.residue_eq_zero_iff (r' - r)).mpr h
  rw [map_sub, sub_eq_zero] at hz
  exact hz

end Galois

end

end Work.SilvermanReduction
