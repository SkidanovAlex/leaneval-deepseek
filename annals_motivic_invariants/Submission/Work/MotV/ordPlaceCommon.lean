/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# The order of vanishing at a rational place: common layer

This file holds the definitions and the elementary lemmas shared by the proof of the API of
`Work.MotV.ordOfPlace` (module `Submission.Work.MotV.ordPlaceAPI`) and its helper lemmas.

The definition `MotV.ordOfPlace` of `Submission/Work/MotV/PlaceDefs.lean` is written with an
internal `letI : IsDiscreteValuationRing ↥S := hS.1.choose` and with
`(IsDiscreteValuationRing.addVal ↥S x).untopD 0`.  For the (many) manipulation lemmas it is
convenient to have

* `MotV.avNat x`, the `ℕ`-valued order of an element `x` of a discrete valuation ring
  (`(addVal R x).untopD 0`, so `0` for `x = 0`), together with the bridge lemmas
  `coe_avNat` (`avNat x` is the natural number whose image is `addVal R x` for `x ≠ 0`) and
  `avNat_mul` (multiplicativity);
* `MotV.ordPlace E S hS f`, a definitionally equal copy of `ordOfPlace E S hS f` phrased with
  `avNat` and with the discrete valuation ring instance as an explicit type class argument —
  this is the version all the structure lemmas are stated for.

## Main results

* `ordOfPlace_eq_ordPlace`
* `ordPlace_eq_of_mem`, `ordPlace_eq_of_notMem`

## Tags

elliptic curve, function field, place, discrete valuation ring, order of vanishing
-/

import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotC2.Classification

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero Classical

namespace Work.MotV

noncomputable section

set_option autoImplicit false

variable {N : Type*} [Field N]

/-! ## §1 The additive valuation of a discrete valuation ring as a `ℕ`-valued function -/

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- `avNat x` is the order of `x` at the valuation of the discrete valuation ring `R`; it is
`0` when `x = 0`, and for `x ≠ 0` it is the natural number with
`(avNat x : ℕ∞) = addVal R x`. -/
def avNat (x : R) : ℕ := (IsDiscreteValuationRing.addVal R x).untopD 0

lemma avNat_def (x : R) : avNat x = (IsDiscreteValuationRing.addVal R x).untopD 0 := rfl

lemma addVal_ne_top_of_ne_zero {x : R} (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal R x ≠ ⊤ :=
  fun h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)

/-- For `x ≠ 0`, `avNat x` is the natural number whose image in `ℕ∞` is `addVal R x`. -/
lemma coe_avNat {x : R} (hx : x ≠ 0) :
    ((avNat x : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal R x := by
  rcases WithTop.untopD_eq_iff.mp (show (IsDiscreteValuationRing.addVal R x).untopD 0 =
      (IsDiscreteValuationRing.addVal R x).untopD 0 from rfl) with h | ⟨h, -⟩
  · exact h.symm
  · exact absurd h (addVal_ne_top_of_ne_zero hx)

lemma avNat_zero : avNat (0 : R) = 0 := by
  rw [avNat_def, IsDiscreteValuationRing.addVal_zero]
  exact WithTop.untopD_top 0

lemma avNat_one : avNat (1 : R) = 0 := by
  rw [avNat_def, IsDiscreteValuationRing.addVal_one]
  exact WithTop.untopD_coe 0 0

/-- `avNat x = 0` exactly for units (and `x ≠ 0`). -/
lemma avNat_eq_zero_iff {x : R} (hx : x ≠ 0) : avNat x = 0 ↔ IsUnit x := by
  rw [← Nat.cast_eq_zero (R := ℕ∞), coe_avNat hx]
  exact IsDiscreteValuationRing.addVal_eq_zero_iff

/-- A non-unit nonzero element has strictly positive order. -/
lemma one_le_avNat_iff {x : R} (hx : x ≠ 0) : 1 ≤ avNat x ↔ ¬ IsUnit x := by
  constructor
  · rintro h1 hu
    have h0 : avNat x = 0 := (avNat_eq_zero_iff hx).mpr hu
    omega
  · intro hu
    have h0 : avNat x ≠ 0 := fun h => hu ((avNat_eq_zero_iff hx).mp h)
    omega

lemma avNat_eq_zero_of_unit (u : Rˣ) : avNat (u : R) = 0 :=
  (avNat_eq_zero_iff (Units.ne_zero u)).mpr u.isUnit

/-- Multiplicativity of the order. -/
lemma avNat_mul {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    avNat (x * y) = avNat x + avNat y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have key : ((avNat (x * y) : ℕ) : ℕ∞) = ((avNat x + avNat y : ℕ) : ℕ∞) :=
    calc ((avNat (x * y) : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal R (x * y) := coe_avNat hxy
      _ = IsDiscreteValuationRing.addVal R x + IsDiscreteValuationRing.addVal R y :=
            IsDiscreteValuationRing.addVal_mul
      _ = ((avNat x : ℕ) : ℕ∞) + ((avNat y : ℕ) : ℕ∞) := by rw [coe_avNat hx, coe_avNat hy]
      _ = ((avNat x + avNat y : ℕ) : ℕ∞) := (WithTop.coe_add (avNat x) (avNat y)).symm
  exact Nat.cast_injective key

/-- The order of a unit times a power of the uniformizer. -/
lemma avNat_unit_mul_pow {u : Rˣ} {π : R} (n : ℕ) :
    avNat ((u : R) * π ^ n) = avNat (π ^ n) := by
  rcases n with _ | n
  · rw [pow_zero, mul_one, avNat_eq_zero_of_unit u, avNat_one]
  · by_cases hπ : π = 0
    · rw [hπ, zero_pow (Nat.succ_ne_zero n), mul_zero]
    · rw [avNat_mul (Units.ne_zero u) (pow_ne_zero (n + 1) hπ), avNat_eq_zero_of_unit u, zero_add]

end DVR

/-! ## §2 The order at a rational place, in `avNat` normal form -/

variable (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))

/-- The order of vanishing of `f : N(E)` at the rational place `S`, phrased with `avNat`:
this is definitionally the same function as `ordOfPlace` (see `ordOfPlace_eq_ordPlace`), but
with the discrete valuation ring structure of `↥S` an explicit type class argument. -/
def ordPlace [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) (f : MotC2.Func E) : ℤ :=
  if hf : f ∈ S then ((avNat (⟨f, hf⟩ : ↥S) : ℕ) : ℤ)
  else -((avNat (⟨f⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ : ↥S) : ℕ) : ℤ)

/-- `ordPlace` is `ordOfPlace`. -/
lemma ordOfPlace_eq_ordPlace [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S)
    (f : MotC2.Func E) : ordOfPlace E S hS f = ordPlace E S hS f := rfl

/-- The membership proof of `f⁻¹ ∈ S` for `f ∉ S`, from the fraction field property. -/
lemma inv_mem_of_notMem {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    (hS : MotC2.IsRatPlace E S) {f : MotC2.Func E} (hf : f ∉ S) : f⁻¹ ∈ S :=
  (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf

/-- The value of `ordPlace` on an element of the place. -/
lemma ordPlace_eq_of_mem [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S)
    (f : MotC2.Func E) (hf : f ∈ S) :
    ordPlace E S hS f = ((avNat (⟨f, hf⟩ : ↥S) : ℕ) : ℤ) := by
  rw [ordPlace]
  simp only [dif_pos hf]

/-- The value of `ordPlace` on an element outside the place. -/
lemma ordPlace_eq_of_notMem [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S)
    (f : MotC2.Func E) (hf : f ∉ S) :
    ordPlace E S hS f =
      -((avNat (⟨f⁻¹, inv_mem_of_notMem hS hf⟩ : ↥S) : ℕ) : ℤ) := by
  rw [ordPlace]
  simp only [dif_neg hf]

lemma ordPlace_zero [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) :
    ordPlace E S hS 0 = 0 := by
  rw [ordPlace_eq_of_mem E S hS 0 S.zero_mem]
  show (((avNat (0 : ↥S) : ℕ)) : ℤ) = 0
  rw [avNat_zero]
  norm_num

lemma ordPlace_one [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) :
    ordPlace E S hS 1 = 0 := by
  rw [ordPlace_eq_of_mem E S hS 1 S.one_mem]
  show (((avNat (1 : ↥S) : ℕ)) : ℤ) = 0
  rw [avNat_one]
  norm_num

end

end Work.MotV
