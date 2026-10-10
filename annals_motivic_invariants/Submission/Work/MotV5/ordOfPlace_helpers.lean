/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotV5.placeVal_valuation
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!

# The elementary API of the order of vanishing at a rational place

`Work.MotV.ordOfPlace E S hS : MotC2.Func E → ℤ` is the order of vanishing of an element of the
function field `N(E)` at the rational place `S`.  By definition

```
ordOfPlace E S hS f = if f ∈ S then (addVal ↥S f).toNat else -(addVal ↥S f⁻¹).toNat
```

where `addVal ↥S : ↥S → ℕ∞` is the additive valuation of the discrete valuation ring `↥S`.

This file collects the elementary facts about `ordOfPlace` that only unfold the definition and use
the basic theory of `IsDiscreteValuationRing.addVal`:

* `ordS E S hS f` : the value `(addVal ↥S f).toNat : ℕ` of an element `f ∈ S` (so that
  `ordOfPlace E S hS f = (ordS E S hS f : ℤ)` for `f ∈ S`);
* `ordOfPlace_of_mem`, `ordOfPlace_of_notMem` : the two cases of the definition;
* `ordS_mul`, `ordOfPlace_mul_of_mem` : additivity of `ordS` (hence of `ordOfPlace` on two
  elements of `S`) on products;
* `ordOfPlace_nonneg_iff` : `0 ≤ ordOfPlace f ↔ f ∈ S`;
* `ordOfPlace_mul`, `ordOfPlace_inv` : multiplicativity of `ordOfPlace` and the behaviour of
  inverses;
* `addVal_lt_add` : the strict triangle inequality for `addVal` in a discrete valuation ring.

## Route for the remaining items

The remaining conjuncts of the API (`ordOfPlace_add`, `ordOfPlace_add_eq_of_lt`,
`ordOfPlace_algebraMap`, `ordOfPlace_residue`) are proved by the following observations.

* **The non-archimedean inequality.**  For `f + g ≠ 0` one proves
  `min (ordOfPlace f) (ordOfPlace g) ≤ ordOfPlace (f + g)` by reducing to the case where both
  factors lie in `S`: if `x, y ∈ S` are non-zero then `ordOfPlace (x + y) = ordS (x + y)` and
  `min (ordS x) (ordS y) = min (ordOfPlace x) (ordOfPlace y)` (the coercion `ℕ → ℤ` commutes with
  `min`), so `IsDiscreteValuationRing.addVal_add` applies; if `g ∉ S` put `v = g⁻¹ ∈ S` and use
  `x + y = (x·v + 1)/v` (or `f + g = (u+v)/(uv)` with `u = f⁻¹`, `v = g⁻¹` when both are outside
  `S`) together with multiplicativity on elements of `S`.
* **The strict case** follows from the non-archimedean inequality applied twice: if
  `ordOfPlace f < ordOfPlace g` and `ordOfPlace (f + g) > ordOfPlace f`, then
  `f = (f + g) + (-g)` gives a contradiction, using `ordOfPlace (-g) = ordOfPlace g`.
* **The constants.**  If `c ≠ 0` then the residue class of `algebraMap N (MotC2.Func E) c` in
  `↥S ⧸ 𝔪` is non-zero by injectivity of `c ↦ mk (algebraMap N ↥S c)`
  (`hS.1.choose_spec.1`), hence `algebraMap N (MotC2.Func E) c` is a unit of `↥S`
  (`IsLocalRing.notMem_maximalIdeal`), and `addVal` of a unit is `0`.
* **The residue of a regular function.**  If `0 ≤ ordOfPlace f` then `f ∈ S`
  (`ordOfPlace_nonneg_iff`), and surjectivity of `c ↦ mk (algebraMap N ↥S c)`
  (`hS.1.choose_spec.2`) produces `c : N` with `f - algebraMap N (MotC2.Func E) c ∈ 𝔪`; if this
  element is non-zero it is a non-unit, so its `addVal` is `≥ 1`.
-/

namespace Work.MotV5

open WeierstrassCurve
open scoped WithZero

variable {N : Type*} [Field N]

namespace OrdAPI

/-! ## The additive valuation of a discrete valuation ring -/

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- `addVal R x` is infinite exactly for `x = 0`. -/
theorem addVal_ne_top (x : R) :
    IsDiscreteValuationRing.addVal R x ≠ ⊤ ↔ x ≠ 0 :=
  (IsDiscreteValuationRing.addVal_eq_top_iff (R := R)).not

/-- `addVal` of a negative element. -/
theorem addVal_neg (x : R) :
    IsDiscreteValuationRing.addVal R (-x) = IsDiscreteValuationRing.addVal R x := by
  rw [show -x = (-1) * x by ring, IsDiscreteValuationRing.addVal_mul]
  have h : IsDiscreteValuationRing.addVal R (-1 : R) = 0 := by
    have hunit := IsDiscreteValuationRing.addVal_eq_zero_of_unit
      (IsUnit.unit (isUnit_neg_one : IsUnit (-1 : R)))
    have hspec : (↑(IsUnit.unit (isUnit_neg_one : IsUnit (-1 : R))) : R) = -1 :=
      IsUnit.unit_spec _
    rwa [hspec] at hunit
  rw [h, zero_add]

/-- The strict triangle inequality for `addVal`: if the value at `y` is strictly larger than the
value at `x`, then the value at `x - y` is the value at `x`. -/
theorem addVal_lt_add {x y : R}
    (h : IsDiscreteValuationRing.addVal R x < IsDiscreteValuationRing.addVal R y) :
    IsDiscreteValuationRing.addVal R (x - y) = IsDiscreteValuationRing.addVal R x := by
  have h1 : min (IsDiscreteValuationRing.addVal R (x - y)) (IsDiscreteValuationRing.addVal R y)
      ≤ IsDiscreteValuationRing.addVal R x := by
    simpa using IsDiscreteValuationRing.addVal_add (a := x - y) (b := y)
  have h2 : min (IsDiscreteValuationRing.addVal R x) (IsDiscreteValuationRing.addVal R y)
      ≤ IsDiscreteValuationRing.addVal R (x - y) := by
    have hh := IsDiscreteValuationRing.addVal_add (a := x) (b := -y)
    rw [addVal_neg] at hh
    rwa [sub_eq_add_neg]
  rw [min_eq_left (le_of_lt h)] at h2
  rcases min_le_iff.mp h1 with h3 | h3
  · exact le_antisymm h3 h2
  · exact absurd h3 (not_le_of_gt h)

end DVR

/-! ## The value of an element of the place -/

/-- The order of vanishing of an element `f` of the place `S`, as a natural number.  This is the
`S`-part of `Work.MotV.ordOfPlace`. -/
noncomputable def ordS (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) (f : ↥S) : ℕ :=
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  ENat.toNat (IsDiscreteValuationRing.addVal ↥S f)

/-- `ordOfPlace` at an element of the place: the first case of the definition. -/
theorem ordOfPlace_of_mem (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) (f : Work.MotC2.Func E) (hf : f ∈ S) :
    Work.MotV.ordOfPlace E S hS f = (ordS E S hS ⟨f, hf⟩ : ℤ) := by
  classical
  have hinst : IsDiscreteValuationRing ↥S := hS.1.choose
  rw [Work.MotV.ordOfPlace, dite_eq_left hf]
  rfl

/-- `ordOfPlace` at an element outside the place: the second case of the definition. -/
theorem ordOfPlace_of_notMem (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) (f : Work.MotC2.Func E) (hf : f ∉ S) :
    Work.MotV.ordOfPlace E S hS f = -(ordS E S hS ⟨f⁻¹,
      (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ : ℤ) := by
  classical
  have hinst : IsDiscreteValuationRing ↥S := hS.1.choose
  rw [Work.MotV.ordOfPlace, dite_eq_right hf]
  rfl

/-- `ordS` is additive on products of non-zero elements of the place. -/
theorem ordS_mul (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) (f g : ↥S) (hf : f ≠ 0) (hg : g ≠ 0) :
    ordS E S hS (f * g) = ordS E S hS f + ordS E S hS g := by
  have hinst : IsDiscreteValuationRing ↥S := hS.1.choose
  have hf' : IsDiscreteValuationRing.addVal ↥S f ≠ ⊤ := (addVal_ne_top f).mpr hf
  have hg' : IsDiscreteValuationRing.addVal ↥S g ≠ ⊤ := (addVal_ne_top g).mpr hg
  simp only [ordS]
  rw [IsDiscreteValuationRing.addVal_mul, ENat.toNat_add hf' hg']

/-- `ordS` of the unit of the place is zero. -/
theorem ordS_one (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) : ordS E S hS (1 : ↥S) = 0 := by
  have hinst : IsDiscreteValuationRing ↥S := hS.1.choose
  have h1 : IsDiscreteValuationRing.addVal ↥S (1 : ↥S) = 0 :=
    IsDiscreteValuationRing.addVal_one (R := ↥S)
  simp only [ordS]
  rw [h1, ENat.toNat_zero]

/-- `ordS f = 0` exactly for the units of the place (among non-zero elements). -/
theorem ordS_eq_zero_iff_unit (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) (f : ↥S) (hf : f ≠ 0) :
    ordS E S hS f = 0 ↔ IsUnit f := by
  have hinst : IsDiscreteValuationRing ↥S := hS.1.choose
  simp only [ordS, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
    IsDiscreteValuationRing.addVal_eq_top_iff, hf, or_false]

/-- A unit of the place whose inverse is a given element `f⁻¹` exhibits `f` as an element of the
place: the inverse of a unit of `S`, computed in the function field, is again in `S`. -/
theorem mem_of_isUnit_inv (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    {f : Work.MotC2.Func E} (hf : f⁻¹ ∈ S) (hu : IsUnit (⟨f⁻¹, hf⟩ : ↥S)) :
    f ∈ S := by
  obtain ⟨u, hu'⟩ := hu
  have hcoe : (((u : (↥S)ˣ) : ↥S) : Work.MotC2.Func E) = f⁻¹ := by rw [hu']
  have key := Work.MotC2.subalgebra_coe_unit_inv S u
  rw [hcoe] at key
  simp only [inv_inv] at key
  rw [← key]
  exact ((u⁻¹ : (↥S)ˣ) : ↥S).2

/-- The order of `1`. -/
theorem ordOfPlace_one (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    Work.MotV.ordOfPlace E S hS (1 : Work.MotC2.Func E) = 0 := by
  rw [ordOfPlace_of_mem E S hS 1 S.one_mem]
  have hsub : (⟨(1 : Work.MotC2.Func E), S.one_mem⟩ : ↥S) = 1 := rfl
  rw [hsub, ordS_one, Nat.cast_zero]

/-- Additivity of the order on a product of two elements of the place. -/
theorem ordOfPlace_mul_of_mem (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) {x y : Work.MotC2.Func E} (hx : x ∈ S) (hy : y ∈ S)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    Work.MotV.ordOfPlace E S hS (x * y) = Work.MotV.ordOfPlace E S hS x +
      Work.MotV.ordOfPlace E S hS y := by
  rw [ordOfPlace_of_mem E S hS (x * y) (mul_mem hx hy),
      ordOfPlace_of_mem E S hS x hx, ordOfPlace_of_mem E S hS y hy]
  have hxne : (⟨x, hx⟩ : ↥S) ≠ 0 := fun h => hx0 (Subtype.ext_iff.mp h)
  have hyne : (⟨y, hy⟩ : ↥S) ≠ 0 := fun h => hy0 (Subtype.ext_iff.mp h)
  rw [show (⟨x * y, mul_mem hx hy⟩ : ↥S) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl,
      ordS_mul E S hS _ _ hxne hyne]
  push_cast
  first | refl_ring1 | ring

/-! ## The first conjuncts of the API -/

/-- **Multiplicativity** of the order of vanishing at a rational place. -/
theorem ordOfPlace_mul (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    ∀ f g : Work.MotC2.Func E, f ≠ 0 → g ≠ 0 →
      Work.MotV.ordOfPlace E S hS (f * g) = Work.MotV.ordOfPlace E S hS f +
        Work.MotV.ordOfPlace E S hS g := by
  have key_left : ∀ {x y : Work.MotC2.Func E}, x ∈ S → x ≠ 0 → y ≠ 0 →
      Work.MotV.ordOfPlace E S hS (x * y) = Work.MotV.ordOfPlace E S hS x +
        Work.MotV.ordOfPlace E S hS y := by
    intro x y hx hx0 hy0
    by_cases hy : y ∈ S
    · exact ordOfPlace_mul_of_mem E S hS hx hy hx0 hy0
    · have hyi : y⁻¹ ∈ S := (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS y).resolve_left hy
      have hyi0 : y⁻¹ ≠ 0 := inv_ne_zero hy0
      have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
      by_cases hxy : x * y ∈ S
      · have h1 := ordOfPlace_mul_of_mem E S hS hxy hyi hxy0 hyi0
        rw [mul_inv_cancel_right₀ hy0] at h1
        simp only [ordOfPlace_of_mem E S hS (x * y) hxy, ordOfPlace_of_mem E S hS x hx,
          ordOfPlace_of_notMem E S hS y hy, ordOfPlace_of_mem E S hS y⁻¹ hyi] at h1 ⊢
        linarith
      · have hxyi : (x * y)⁻¹ ∈ S :=
          (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS (x * y)).resolve_left hxy
        have hxyi0 : (x * y)⁻¹ ≠ 0 := inv_ne_zero hxy0
        have h1 := ordOfPlace_mul_of_mem E S hS hx hxyi hx0 hxyi0
        have hcalc : x * (x * y)⁻¹ = y⁻¹ := by field_simp
        rw [hcalc] at h1
        simp only [ordOfPlace_of_mem E S hS x hx, ordOfPlace_of_mem E S hS (x * y)⁻¹ hxyi,
          ordOfPlace_of_mem E S hS y⁻¹ hyi, ordOfPlace_of_notMem E S hS (x * y) hxy,
          ordOfPlace_of_notMem E S hS y hy] at h1 ⊢
        linarith
  intro f g hf0 hg0
  by_cases hf : f ∈ S
  · exact key_left hf hf0 hg0
  · by_cases hg : g ∈ S
    · rw [mul_comm, key_left hg hg0 hf0]; ring
    · have hgi : g⁻¹ ∈ S := (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS g).resolve_left hg
      have hfi : f⁻¹ ∈ S := (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf
      have hfg : f * g ∉ S := fun hcon => hf (by
        have hfe : f = (f * g) * g⁻¹ := by field_simp
        rw [hfe]; exact mul_mem hcon hgi)
      have hfgi : (f * g)⁻¹ ∈ S :=
        (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS (f * g)).resolve_left hfg
      have h1 := ordOfPlace_mul_of_mem E S hS hfi hgi (inv_ne_zero hf0) (inv_ne_zero hg0)
      have hcalc : f⁻¹ * g⁻¹ = (f * g)⁻¹ := by field_simp
      rw [hcalc] at h1
      simp only [ordOfPlace_of_mem E S hS f⁻¹ hfi, ordOfPlace_of_mem E S hS g⁻¹ hgi,
        ordOfPlace_of_mem E S hS (f * g)⁻¹ hfgi, ordOfPlace_of_notMem E S hS (f * g) hfg,
        ordOfPlace_of_notMem E S hS f hf, ordOfPlace_of_notMem E S hS g hg] at h1 ⊢
      linarith

/-- The order of an inverse is the negative of the order. -/
theorem ordOfPlace_inv (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    ∀ f : Work.MotC2.Func E, f ≠ 0 →
      Work.MotV.ordOfPlace E S hS f⁻¹ = - Work.MotV.ordOfPlace E S hS f := by
  intro f hf0
  have hfi0 : f⁻¹ ≠ 0 := inv_ne_zero hf0
  by_cases hf : f ∈ S
  · by_cases hfi : f⁻¹ ∈ S
    · have h1 := ordOfPlace_mul_of_mem E S hS hf hfi hf0 hfi0
      rw [mul_inv_cancel₀ hf0, ordOfPlace_one] at h1
      simp only [ordOfPlace_of_mem E S hS f hf, ordOfPlace_of_mem E S hS f⁻¹ hfi] at h1 ⊢
      linarith
    · have h := ordOfPlace_of_notMem E S hS f⁻¹ hfi
      simp only [inv_inv] at h
      rw [h, ordOfPlace_of_mem E S hS f hf]
  · have hfi : f⁻¹ ∈ S := (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf
    simp only [ordOfPlace_of_notMem E S hS f hf, ordOfPlace_of_mem E S hS f⁻¹ hfi] at ⊢
    first | refl_ring1 | ring

/-- The order is non-negative exactly on the place. -/
theorem ordOfPlace_nonneg_iff (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    ∀ f : Work.MotC2.Func E, 0 ≤ Work.MotV.ordOfPlace E S hS f ↔ f ∈ S := by
  intro f
  constructor
  · intro h
    by_contra hf
    have h1 := ordOfPlace_of_notMem E S hS f hf
    rw [h1] at h
    have h2 : ordS E S hS ⟨f⁻¹,
        (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ = 0 := by
      have := Nat.zero_le (ordS E S hS ⟨f⁻¹,
        (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩)
      omega
    have hf0 : f ≠ 0 := fun h0 => hf (h0 ▸ S.zero_mem)
    have hne : (⟨f⁻¹, (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ : ↥S) ≠ 0 := by
      intro hh
      exact inv_ne_zero hf0 (Subtype.ext_iff.mp hh)
    exact hf (mem_of_isUnit_inv E S _ ((ordS_eq_zero_iff_unit E S hS _ hne).mp h2))
  · intro hf
    rw [ordOfPlace_of_mem E S hS f hf]
    exact Int.natCast_nonneg _

/-- The order of `0` is `0`, the convention of the definition (`addVal 0 = ⊤` and `toNat ⊤ = 0`). -/
theorem ordOfPlace_zero (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    Work.MotV.ordOfPlace E S hS (0 : Work.MotC2.Func E) = 0 := by
  rw [ordOfPlace_of_mem E S hS 0 S.zero_mem]
  have hzero : (⟨(0 : Work.MotC2.Func E), S.zero_mem⟩ : ↥S) = 0 := rfl
  have hinst : IsDiscreteValuationRing ↥S := hS.1.choose
  have h1 : IsDiscreteValuationRing.addVal ↥S (0 : ↥S) = ⊤ :=
    IsDiscreteValuationRing.addVal_zero (R := ↥S)
  simp only [ordS, hzero, h1, ENat.toNat_top, Nat.cast_zero]

/-- **The non-archimedean (ultrametric) inequality** for the order at a rational place, obtained
from `Valuation.map_add` of the valuation `placeValuation E S hS` whose value on `f ≠ 0` is
`exp (-(ordOfPlace E S hS f))`. -/
theorem ordOfPlace_add (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    ∀ f g : Work.MotC2.Func E, f + g ≠ 0 →
      min (Work.MotV.ordOfPlace E S hS f) (Work.MotV.ordOfPlace E S hS g) ≤
        Work.MotV.ordOfPlace E S hS (f + g) := by
  intro f g hfg
  rcases eq_or_ne f 0 with rfl | hf
  · rw [zero_add, ordOfPlace_zero]
    exact min_le_right _ _
  rcases eq_or_ne g 0 with rfl | hg
  · rw [add_zero, ordOfPlace_zero]
    exact min_le_left _ _
  have key : WithZero.exp (-(Work.MotV.ordOfPlace E S hS (f + g))) ≤
      WithZero.exp (-(min (Work.MotV.ordOfPlace E S hS f)
        (Work.MotV.ordOfPlace E S hS g))) := by
    calc WithZero.exp (-(Work.MotV.ordOfPlace E S hS (f + g)))
        = placeValuation E S hS (f + g) :=
          (placeValuation_apply E S hS (f + g) hfg).symm
      _ ≤ max (placeValuation E S hS f) (placeValuation E S hS g) :=
          Valuation.map_add (placeValuation E S hS) f g
      _ ≤ WithZero.exp (-(min (Work.MotV.ordOfPlace E S hS f)
            (Work.MotV.ordOfPlace E S hS g))) := by
          apply max_le
          · rw [placeValuation_apply E S hS f hf]
            exact WithZero.exp_le_exp.mpr (by simp)
          · rw [placeValuation_apply E S hS g hg]
            exact WithZero.exp_le_exp.mpr (by simp)
  have := WithZero.exp_le_exp.mp key
  linarith

/-- **No cancellation**: if the orders of `f` and `g` differ strictly, then the order of the sum
is the smaller one.  This is `Valuation.map_add_eq_of_lt_left` for `placeValuation E S hS`. -/
theorem ordOfPlace_add_eq_of_lt (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    ∀ f g : Work.MotC2.Func E, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      Work.MotV.ordOfPlace E S hS f < Work.MotV.ordOfPlace E S hS g →
      Work.MotV.ordOfPlace E S hS (f + g) = Work.MotV.ordOfPlace E S hS f := by
  intro f g hf0 hg0 hfg hlt
  have hlt' : placeValuation E S hS g < placeValuation E S hS f := by
    rw [placeValuation_apply E S hS g hg0, placeValuation_apply E S hS f hf0,
      WithZero.exp_lt_exp]
    omega
  have hadd : placeValuation E S hS (f + g) = placeValuation E S hS f :=
    Valuation.map_add_eq_of_lt_left (placeValuation E S hS) hlt'
  have h1 : WithZero.exp (-(Work.MotV.ordOfPlace E S hS (f + g))) =
      WithZero.exp (-(Work.MotV.ordOfPlace E S hS f)) := by
    rw [← placeValuation_apply E S hS (f + g) hfg, ← placeValuation_apply E S hS f hf0, hadd]
  exact neg_injective (WithZero.exp_inj.mp h1)

/-- **The order of a non-zero constant** is `0`: a non-zero constant is a unit of the place, so its
`addVal` vanishes.  (Obtained from `placeVal_valuation`, where it is the triviality of the place on
the base field.) -/
theorem ordOfPlace_algebraMap (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    ∀ c : N, c ≠ 0 →
      Work.MotV.ordOfPlace E S hS (algebraMap N (Work.MotC2.Func E) c) = 0 := by
  intro c hc
  obtain ⟨_, hvT, hv1, -, -⟩ := placeVal_valuation E S hS
  have hc0 : algebraMap N (Work.MotC2.Func E) c ≠ 0 := fun h =>
    hc ((FaithfulSMul.algebraMap_injective N (Work.MotC2.Func E)) (by simpa using h))
  have h1 : WithZero.exp (-(Work.MotV.ordOfPlace E S hS (algebraMap N (Work.MotC2.Func E) c))) =
      1 := by
    rw [← hv1 _ hc0, hvT c hc]
  rw [← WithZero.exp_zero] at h1
  have := WithZero.exp_inj.mp h1
  linarith

/-- **The residue of a regular function is a constant**: if `0 ≤ ordOfPlace f` then `f` lies in the
place, and the residue field of `S` is `N` through the constants, so there is `c : N` with
`f - c` in the maximal ideal (hence of order at least one), unless `f` is itself the constant. -/
theorem ordOfPlace_residue (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    ∀ f : Work.MotC2.Func E, 0 ≤ Work.MotV.ordOfPlace E S hS f →
      ∃ c : N, f = algebraMap N (Work.MotC2.Func E) c ∨
        1 ≤ Work.MotV.ordOfPlace E S hS (f - algebraMap N (Work.MotC2.Func E) c) := by
  intro f hf
  have hfS : f ∈ S := (ordOfPlace_nonneg_iff E S hS f).mp hf
  obtain ⟨hDVR, hbij⟩ := hS.1
  letI : IsDiscreteValuationRing ↥S := hDVR
  obtain ⟨c, hc⟩ := hbij.2 (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥S) (⟨f, hfS⟩ : ↥S))
  refine ⟨c, ?_⟩
  by_cases h : f = algebraMap N (Work.MotC2.Func E) c
  · exact Or.inl h
  · right
    have hx : f - algebraMap N (Work.MotC2.Func E) c ∈ S :=
      Subalgebra.sub_mem _ hfS (Subalgebra.algebraMap_mem _ c)
    have hx0 : f - algebraMap N (Work.MotC2.Func E) c ≠ 0 := sub_ne_zero.mpr h
    have hcoe : (⟨f - algebraMap N (Work.MotC2.Func E) c, hx⟩ : ↥S) =
        (⟨f, hfS⟩ : ↥S) - algebraMap N ↥S c := by
      apply Subtype.ext
      simp
    have hne : (⟨f, hfS⟩ : ↥S) - algebraMap N ↥S c ≠ 0 := by
      rw [← hcoe]
      exact fun hh => hx0 (Subtype.ext_iff.mp hh)
    have hmem : (⟨f, hfS⟩ : ↥S) - algebraMap N ↥S c ∈ IsLocalRing.maximalIdeal ↥S := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc, sub_self]
    have hnu : ¬ IsUnit ((⟨f, hfS⟩ : ↥S) - algebraMap N ↥S c) := fun hu =>
      (IsLocalRing.notMem_maximalIdeal.mpr hu) hmem
    have h0 : ordS E S hS ((⟨f, hfS⟩ : ↥S) - algebraMap N ↥S c) ≠ 0 := fun hz =>
      hnu ((ordS_eq_zero_iff_unit E S hS _ hne).mp hz)
    rw [ordOfPlace_of_mem E S hS (f - algebraMap N (Work.MotC2.Func E) c) hx, hcoe,
      ← Nat.cast_one]
    exact_mod_cast Nat.pos_of_ne_zero h0

end OrdAPI

end Work.MotV5
