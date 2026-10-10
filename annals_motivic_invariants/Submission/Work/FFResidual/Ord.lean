/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The order of vanishing at a place of a function field

For a place `P : FunctionFieldPlace 𝔽 𝕜` (a discrete valuation ring `R ⊆ 𝕜` with fraction field
`𝕜`), this file introduces the **order of vanishing** `P.ord : 𝕜 → ℤ` at the place, normalized so
that the chosen uniformizer has order `1`, and develops the API used by the function-field classes
(b), (c), (d):

* `FunctionFieldPlace.ord_mul`, `ord_add_le`, `ord_add_eq_min` — the valuation axioms;
* `FunctionFieldPlace.ord_nonneg_iff` — `ord x ≥ 0` iff `x` is integral (`x` lifts to `R`);
* `FunctionFieldPlace.ord_uniformizer` — `ord π = 1`;
* `FunctionFieldPlace.not_exists_pow_five_uniformizer` — the uniformizer is not a fifth power
  (the Kummer input of the classes (b), (c), (d));
* `FunctionFieldPlace.not_exists_artinSchreier_inv_uniformizer` — `1 / π` is not an Artin–Schreier
  value (the characteristic-`5` input).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false


open scoped WithZero

namespace Work.FFResidual

noncomputable section

open Work.SilvermanReduction

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]
  (P : FunctionFieldPlace 𝔽 𝕜)

/-- **The order of vanishing at the place**, as a `ℤ`-valued function: the additive logarithm of
the `ℤᵐ⁰`-valued valuation `val P.R 𝕜`, with the junk value `0` at `0`.

It is normalized so that the chosen uniformizer `P.π` has order `1`
(`FunctionFieldPlace.ord_uniformizer`), i.e. `ord x ≥ 0` for the integral elements and
`ord x > 0` for the elements of the maximal ideal. -/
noncomputable def ord (x : 𝕜) : ℤ := -(val P.R 𝕜 x).log

variable {P}

@[simp]
theorem ord_zero : P.ord 0 = 0 := by simp [ord]

@[simp]
theorem ord_one : P.ord 1 = 0 := by simp [ord]

theorem val_ne_zero_iff {x : 𝕜} : val P.R 𝕜 x ≠ 0 ↔ x ≠ 0 :=
  Valuation.ne_zero_iff _

theorem ord_mul {x y : 𝕜} (hx : x ≠ 0) (hy : y ≠ 0) : P.ord (x * y) = P.ord x + P.ord y := by
  have hx' : val P.R 𝕜 x ≠ 0 := P.val_ne_zero_iff.mpr hx
  have hy' : val P.R 𝕜 y ≠ 0 := P.val_ne_zero_iff.mpr hy
  simp only [ord, map_mul, WithZero.log_mul hx' hy']
  first | refl_ring1 | ring

theorem ord_pow {x : 𝕜} (hx : x ≠ 0) (n : ℕ) : P.ord (x ^ n) = n * P.ord x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ord_mul (pow_ne_zero _ hx) hx, ih]
    push_cast
    first | refl_ring1 | ring

theorem ord_inv {x : 𝕜} (hx : x ≠ 0) : P.ord x⁻¹ = -P.ord x := by
  have h : P.ord (x⁻¹ * x) = P.ord x⁻¹ + P.ord x :=
    ord_mul (inv_ne_zero hx) hx
  rw [inv_mul_cancel₀ hx, ord_one] at h
  linarith

theorem ord_neg (x : 𝕜) : P.ord (-x) = P.ord x := by
  simp only [ord, Valuation.map_neg]

/-- **The triangle inequality** at a place: the order of a sum is at least the minimum of the
orders. -/
theorem ord_add_le {x y : 𝕜} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (P.ord x) (P.ord y) ≤ P.ord (x + y) := by
  have hx' : val P.R 𝕜 x ≠ 0 := P.val_ne_zero_iff.mpr hx
  have hy' : val P.R 𝕜 y ≠ 0 := P.val_ne_zero_iff.mpr hy
  have hxy' : val P.R 𝕜 (x + y) ≠ 0 := P.val_ne_zero_iff.mpr hxy
  have hle : val P.R 𝕜 (x + y) ≤ max (val P.R 𝕜 x) (val P.R 𝕜 y) := Valuation.map_add _ x y
  rcases le_total (val P.R 𝕜 x) (val P.R 𝕜 y) with h | h
  · have hlog : (val P.R 𝕜 (x + y)).log ≤ (val P.R 𝕜 y).log :=
      (WithZero.log_le_log hxy' hy').mpr (by rwa [max_eq_right h] at hle)
    have hlogx : (val P.R 𝕜 x).log ≤ (val P.R 𝕜 y).log :=
      (WithZero.log_le_log hx' hy').mpr h
    simp only [ord]
    rw [min_eq_right (by linarith)]
    linarith
  · have hlog : (val P.R 𝕜 (x + y)).log ≤ (val P.R 𝕜 x).log :=
      (WithZero.log_le_log hxy' hx').mpr (by rwa [max_eq_left h] at hle)
    have hlogx : (val P.R 𝕜 y).log ≤ (val P.R 𝕜 x).log :=
      (WithZero.log_le_log hy' hx').mpr h
    simp only [ord]
    rw [min_eq_left (by linarith)]
    linarith

/-- **The strict triangle inequality**: if the orders of `x` and `y` differ, then the order of the
sum is the minimum. -/
theorem ord_add_eq_of_lt {x y : 𝕜} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (hlt : P.ord x < P.ord y) : P.ord (x + y) = P.ord x := by
  have h2 : P.ord (x + y) ≤ P.ord x := by
    by_contra hcon
    push_neg at hcon
    have h3 := P.ord_add_le (x := x + y) (y := -y) hxy (neg_ne_zero.mpr hy)
      (by simpa [add_neg_cancel_right] using hx)
    rw [add_neg_cancel_right, ord_neg] at h3
    exact absurd h3 (not_le.mpr (lt_min hcon hlt))
  have h1 : P.ord x ≤ P.ord (x + y) := by
    have h := P.ord_add_le hx hy hxy
    rwa [min_eq_left hlt.le] at h
  exact le_antisymm h2 h1

/-- **The strict triangle inequality**: if the orders of `x` and `y` differ, then the order of the
sum is the minimum. -/
theorem ord_add_eq_min {x y : 𝕜} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (hne : P.ord x ≠ P.ord y) : P.ord (x + y) = min (P.ord x) (P.ord y) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [ord_add_eq_of_lt hx hy hxy h, min_eq_left h.le]
  · rw [add_comm, ord_add_eq_of_lt hy hx (by rwa [add_comm]) h, min_eq_right h.le]

/-- **An element is integral at the place iff its order is nonnegative.** -/
theorem ord_nonneg_iff (x : 𝕜) : 0 ≤ P.ord x ↔ ∃ r : P.R, algebraMap P.R 𝕜 r = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : val P.R 𝕜 x ≠ 0 := P.val_ne_zero_iff.mpr hx
    have h : 0 ≤ P.ord x ↔ val P.R 𝕜 x ≤ 1 := by
      rw [ord, neg_nonneg, ← WithZero.log_one,
        WithZero.log_le_log hx' (one_ne_zero : (1 : ℤᵐ⁰) ≠ 0)]
    rw [h]
    exact IsIntegralK.iff_exists x

/-- **The order of a nonzero element of `R` is zero iff it is a unit.** -/
theorem ord_algebraMap_eq_zero_iff {r : P.R} (hr : r ≠ 0) :
    P.ord (algebraMap P.R 𝕜 r) = 0 ↔ IsUnit r := by
  have hne : algebraMap P.R 𝕜 r ≠ 0 :=
    fun h => hr (IsFractionRing.injective P.R 𝕜 (by simpa using h))
  have hvne : val P.R 𝕜 (algebraMap P.R 𝕜 r) ≠ 0 := P.val_ne_zero_iff.mpr hne
  have h : ((val P.R 𝕜 (algebraMap P.R 𝕜 r)).log = 0)
      ↔ val P.R 𝕜 (algebraMap P.R 𝕜 r) = 1 := by
    constructor
    · intro h
      have := congrArg WithZero.exp h
      rwa [WithZero.exp_log hvne, WithZero.exp_zero] at this
    · intro h; rw [h, WithZero.log_one]
  rw [ord, neg_eq_zero, h, val_algebraMap_eq_one_iff, IsLocalRing.notMem_maximalIdeal]

/-- **The uniformizer has order one.** -/
theorem ord_uniformizer : P.ord (algebraMap P.R 𝕜 P.π) = 1 := by
  have hirr : Irreducible P.π :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal P.π P.pi_ne_zero P.isUniformizer
  have h₁ : Ring.ordFrac P.R (algebraMap P.R 𝕜 P.π) = WithZero.exp 1 :=
    Ring.ordFrac_irreducible hirr
  have h₂ : Ring.ordFrac P.R (algebraMap P.R 𝕜 P.π)
      = (val P.R 𝕜 (algebraMap P.R 𝕜 P.π))⁻¹ :=
    Ring.ordFrac_eq_valuation_inv _
  have h₃ : val P.R 𝕜 (algebraMap P.R 𝕜 P.π) = WithZero.exp (-1) := by
    have h : (val P.R 𝕜 (algebraMap P.R 𝕜 P.π))⁻¹ = WithZero.exp 1 := by rw [← h₂, h₁]
    rw [WithZero.exp_neg, ← h, inv_inv]
  rw [ord, h₃, WithZero.log_exp]
  norm_num

/-- **The uniformizer is not a fifth power** in the function field: the Kummer input of the
function-field classes. -/
theorem not_exists_pow_five_uniformizer :
    ¬ ∃ b : 𝕜, b ^ 5 = algebraMap P.R 𝕜 P.π := by
  rintro ⟨b, hb⟩
  have hne : algebraMap P.R 𝕜 P.π ≠ 0 :=
    fun h => P.pi_ne_zero (IsFractionRing.injective P.R 𝕜 (by simpa using h))
  have hb0 : b ≠ 0 := by rintro rfl; exact hne (by simpa using hb.symm)
  have h : P.ord (b ^ 5) = P.ord (algebraMap P.R 𝕜 P.π) := by rw [hb]
  rw [ord_pow hb0, ord_uniformizer] at h
  omega


/-- **`1 / π` is not an Artin–Schreier value** in the function field: there is no `b` with
`b ^ 5 - b = 1 / π`.  This is the characteristic-`5` input of the function-field classes: at the
place with uniformizer `π`, the element `1 / π` has a simple pole, while `b ^ 5 - b` never does. -/
theorem not_exists_artinSchreier_inv_uniformizer (P : FunctionFieldPlace 𝔽 𝕜) :
    ¬ ∃ b : 𝕜, b ^ 5 - b = (algebraMap P.R 𝕜 P.π)⁻¹ := by
  rintro ⟨b, hb⟩
  have hπ : algebraMap P.R 𝕜 P.π ≠ 0 := fun h =>
    P.pi_ne_zero (IsFractionRing.injective P.R 𝕜 (by simpa using h))
  have hsum : b ^ 5 + (-b) ≠ 0 := by
    intro h
    have h' : b ^ 5 - b = 0 := by rw [sub_eq_add_neg]; exact h
    rw [hb] at h'
    exact (inv_ne_zero hπ) h'
  have hord : P.ord (b ^ 5 + (-b)) = -1 := by
    have h1 : P.ord ((algebraMap P.R 𝕜 P.π)⁻¹) = -1 := by
      rw [ord_inv hπ, ord_uniformizer]
    rwa [← sub_eq_add_neg, hb]
  rcases eq_or_ne b 0 with rfl | hb0
  · have h0 : P.ord (0 : 𝕜) = -1 := by simpa using hord
    rw [P.ord_zero] at h0
    exact absurd h0 (by norm_num)
  · have hb5 : b ^ 5 ≠ 0 := pow_ne_zero 5 hb0
    have hnb : -b ≠ 0 := neg_ne_zero.mpr hb0
    have hpow : P.ord (b ^ 5) = 5 * P.ord b := ord_pow hb0 5
    rcases lt_trichotomy (P.ord b) 0 with hm | hm | hm
    · -- the order of `b` is negative: the term `b ^ 5` dominates
      have hone : P.ord (b ^ 5 + -b) = 5 * P.ord b := by
        rw [P.ord_add_eq_min hb5 hnb hsum (by rw [hpow, ord_neg]; omega), hpow, ord_neg]
        exact min_eq_left (by omega)
      omega
    · -- the order of `b` is zero: `b` is a unit at the place
      by_cases hb4 : b ^ 4 = 1
      · have hzero : b ^ 5 + -b = 0 := by
          rw [← sub_eq_add_neg, show b ^ 5 - b = b * (b ^ 4 - 1) by ring, hb4]
          first | refl_ring1 | ring
        rw [hzero, P.ord_zero] at hord
        norm_num at hord
      · have hb4ne : b ^ 4 - 1 ≠ 0 := fun h => hb4 (sub_eq_zero.mp h)
        have hb4int : 0 ≤ P.ord (b ^ 4 - 1) := by
          have h := P.ord_add_le (pow_ne_zero 4 hb0) (by norm_num : (-1 : 𝕜) ≠ 0)
            (by rw [← sub_eq_add_neg]; exact hb4ne)
          rw [ord_pow hb0 4, hm, ord_neg, ord_one] at h
          simpa [sub_eq_add_neg] using h
        have hmul : P.ord (b ^ 5 + -b) = P.ord b + P.ord (b ^ 4 - 1) := by
          rw [← sub_eq_add_neg, show b ^ 5 - b = b * (b ^ 4 - 1) by ring, ord_mul hb0 hb4ne]
        omega
    · -- the order of `b` is positive: the term `b` dominates
      have hone : P.ord (b ^ 5 + -b) = P.ord b := by
        rw [P.ord_add_eq_min hb5 hnb hsum (by rw [hpow, ord_neg]; omega), hpow, ord_neg]
        exact min_eq_right (by omega)
      omega

end FunctionFieldPlace

end

end Work.FFResidual
