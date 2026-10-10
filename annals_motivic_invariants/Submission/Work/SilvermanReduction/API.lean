/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# API for the reduction map on the points of a Weierstrass curve

Auxiliary lemmas for the proof of Silverman, *AEC*, VII.2.1 in the integral case:
the valuation of a lift and its residue, the chord identity for two points of an integral
Weierstrass equation, and the reduction of a quotient of integral elements.

## Main results

* `chord_identity` — the chord identity `(y₁-y₂)(y₁+y₂+a₁x₁+a₃) = (x₁-x₂)D'`.
* `exists_lift_div` — the residue of a quotient by a unit.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## 1. The valuation of a lift and its residue -/

lemma val_algebraMap_lt_one_iff_residue_eq_zero (r : R) :
    val R K (algebraMap R K r) < 1 ↔ residue R r = 0 := by
  rw [val_algebraMap_lt_one_iff]
  exact (IsLocalRing.residue_eq_zero_iff r).symm

lemma val_algebraMap_eq_one_iff_residue_ne_zero (r : R) :
    val R K (algebraMap R K r) = 1 ↔ residue R r ≠ 0 := by
  rw [val_algebraMap_eq_one_iff]
  exact (not_congr (IsLocalRing.residue_eq_zero_iff r)).symm

lemma isUnit_iff_residue_ne_zero' {r : R} : IsUnit r ↔ residue R r ≠ 0 :=
  (IsLocalRing.residue_ne_zero_iff_isUnit r).symm

lemma val_algebraMap_lt_one_of_not_isUnit {r : R} (h : ¬ IsUnit r) :
    val R K (algebraMap R K r) < 1 := by
  rw [val_algebraMap_lt_one_iff]
  rwa [IsLocalRing.mem_maximalIdeal]

lemma val_algebraMap_eq_one_of_isUnit {r : R} (h : IsUnit r) :
    val R K (algebraMap R K r) = 1 :=
  (val_algebraMap_eq_one_iff_residue_ne_zero r).mpr ((isUnit_iff_residue_ne_zero' (r := r)).mp h)

lemma not_isIntegralK_iff {x : K} : ¬ IsIntegralK R K x ↔ 1 < val R K x :=
  not_le

lemma one_lt_val_of_ne_zero_of_isIntegralK {x : K} (hx : x ≠ 0) (h : ¬ IsIntegralK R K x) :
    1 < val R K x := not_le.mp h

/-! ## 2. Elementary order facts in `ℤᵐ⁰` -/

lemma one_lt_mul_self {a : ℤᵐ⁰} (h : 1 < a) : 1 < a * a := by
  calc (1 : ℤᵐ⁰) = 1 * 1 := (one_mul 1).symm
    _ < a * a := mul_lt_mul'' h h zero_le_one zero_le_one

lemma mul_le_self_of_le_one {a b : ℤᵐ⁰} (ha : a ≤ 1) : a * b ≤ b := by
  calc a * b ≤ 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b

lemma lt_div_self_of_lt_one {a b : ℤᵐ⁰} (ha : (0 : ℤᵐ⁰) < a) (hb : b < 1)
    (hb0 : (0 : ℤᵐ⁰) < b) : a < a / b := by
  rw [lt_div_iff₀ (c := b) hb0]
  calc a * b < a * 1 := mul_lt_mul_of_pos_left hb ha
    _ = a := mul_one a

/-- A nonzero element with valuation `< 1` has valuation strictly smaller than any element
of valuation `1`. -/
lemma lt_one_of_lt_one {a b : ℤᵐ⁰} (ha : a < 1) (hb : b = 1) : a < b := by
  rw [hb]; exact ha

/-! ## 3. The chord identity -/

section Chord

variable {S : Type*} [CommRing S] {W' : Affine S}

/-- **The chord identity.**  For two points of a Weierstrass equation the differences satisfy
`(y₁-y₂)(y₁+y₂+a₁x₁+a₃) = (x₁-x₂)(x₁²+x₁x₂+x₂²+a₂(x₁+x₂)+a₄-a₁y₂)`. -/
theorem chord_identity {x y u v : S} (h : W'.Equation x y) (h' : W'.Equation u v) :
    (y - v) * (y + v + W'.a₁ * x + W'.a₃) =
      (x - u) * (x ^ 2 + x * u + u ^ 2 + W'.a₂ * (x + u) + W'.a₄ - W'.a₁ * v) := by
  have key : (y - v) * (y + v + W'.a₁ * x + W'.a₃) -
      (x - u) * (x ^ 2 + x * u + u ^ 2 + W'.a₂ * (x + u) + W'.a₄ - W'.a₁ * v) = 0 := by
    rw [equation_iff] at h h'
    linear_combination (norm := first | refl_ring1 | ring1) h - h'
  exact sub_eq_zero.mp key

/-- The chord identity with the roles of the two points exchanged. -/
theorem chord_identity' {x y u v : S} (h : W'.Equation x y) (h' : W'.Equation u v) :
    (y - v) * (y + v + W'.a₁ * u + W'.a₃) =
      (x - u) * (u ^ 2 + u * x + x ^ 2 + W'.a₂ * (u + x) + W'.a₄ - W'.a₁ * y) := by
  have key : (y - v) * (y + v + W'.a₁ * u + W'.a₃) -
      (x - u) * (u ^ 2 + u * x + x ^ 2 + W'.a₂ * (u + x) + W'.a₄ - W'.a₁ * y) = 0 := by
    rw [equation_iff] at h h'
    linear_combination (norm := first | refl_ring1 | ring1) h - h'
  exact sub_eq_zero.mp key

end Chord

/-! ## 4. Residues of quotients -/

lemma algebraMap_units_inv (u : Rˣ) :
    algebraMap R K ((u⁻¹ : Rˣ) : R) = ((algebraMap R K (u : R))⁻¹) := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, Units.inv_mul, map_one]

lemma residue_units_inv (u : Rˣ) :
    residue R ((u⁻¹ : Rˣ) : R) = ((residue R (u : R))⁻¹) := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, Units.inv_mul, map_one]

/-- **The residue of a quotient by a unit.**  If `d` is a unit of `R`, then the quotient
`n / d` in `K` is the image of an element `ρ` of `R` whose residue is `residue n / residue d`. -/
theorem exists_lift_div {n d : R} (hd : IsUnit d) :
    ∃ ρ : R, algebraMap R K ρ = algebraMap R K n / algebraMap R K d ∧
      residue R ρ = residue R n / residue R d := by
  obtain ⟨u, rfl⟩ := hd
  refine ⟨n * ((u⁻¹ : Rˣ) : R), ?_, ?_⟩
  · rw [map_mul, div_eq_mul_inv, algebraMap_units_inv]
  · rw [map_mul, div_eq_mul_inv, residue_units_inv]

end

end Work.SilvermanReduction
