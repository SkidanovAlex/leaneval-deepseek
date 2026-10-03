/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A series of order `m` with a unit `m`-th coefficient is invertible

Let `A` be a ring and let `A((t;τ)) = SkewLaurentSeries A` be the skew Laurent series ring of
[JZLA20, §3.1], filtered by `VanishesBelow`.  The main result of this file is the algebraic
statement that *every* series whose leading coefficient is a unit is invertible:

`exists_inverse_of_vanishesBelow_of_coeff_isUnit`: if `f` vanishes below `m` and `f.1 m` is a
unit of `A`, then there is `g` with `f * g = 1`, `g * f = 1` and `VanishesBelow g (-m)`.

This is the general-ring version of `inv_vanishesBelow` (which is stated over a division ring),
and it is proved in two steps.

* First `isUnit_of_vanishesBelow_of_coeff_isUnit`: such an `f` is a unit.  Dividing by the
  monomial `tᵐ` we may assume `m = 0`; then `f = a + x` with `a = f.1 0` a unit and `x` vanishing
  below `1`, so `f = a·(1 + a⁻¹x)` is a unit, a product of the unit `a = coeff a` and the unit
  `1 + (a⁻¹x)` given by the geometric series construction
  (`isUnit_one_add_of_vanishesBelow_one`).

* Second, `vanishesBelow_of_mul_eq_one` reads off the *order* of any two-sided inverse: if
  `g * f = 1` and `g` had a nonzero coefficient at some index `k₀` (the least such), then by
  `mul_apply_leading` the coefficient of degree `k₀ + m` of `g * f = 1` is the single product
  `g.1 k₀ * (k₀ • f.1 m)`.  Its right factor is a unit (the action is by ring automorphisms), so
  the product cannot vanish; hence `k₀ + m = 0`, that is `k₀ = -m`, and the order of `g` is `-m`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow
import Submission.Work.ORHughesFree.SkewLaurentSeries.isUnit_one_add_of_vanishesBelow_one
import Submission.Work.ORHughesFree.SkewLaurentSeries.isUnit_mono_of_isUnit
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff
import Submission.Work.ORHughesFree.SkewLaurentSeries.inv_vanishesBelow

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.SkewLaurentSeries

variable {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]

/-- **The constant-term case.**  If `f` vanishes below `0` and its constant coefficient is a unit
of `A`, then `f` is a unit of `A((t;τ))`.

Indeed, with `a = f.1 0` and `x = f - a·t⁰`, the series `x` vanishes below `0` and has vanishing
constant coefficient, hence vanishes below `1` (`VanishesBelow.succ`); and
`f = a·t⁰ · (1 + a⁻¹·t⁰·x)`, a product of two units, the second because `a⁻¹·t⁰·x` vanishes
below `0 + 1 = 1`. -/
theorem isUnit_of_vanishesBelow_zero_of_coeff_isUnit {f : SkewLaurentSeries A}
    (h : VanishesBelow f 0) (hu : IsUnit (f.1 0)) : IsUnit f := by
  obtain ⟨u, hu_eq⟩ := hu
  -- `x = f - a·t⁰` vanishes below `0` and has zero constant coefficient, hence vanishes below `1`
  have hx0 : VanishesBelow (f - mono 0 (f.1 0)) 0 :=
    VanishesBelow.sub h (mono_vanishesBelow 0 _ le_rfl)
  have hx1 : VanishesBelow (f - mono 0 (f.1 0)) 1 := by
    have hc : (f - mono 0 (f.1 0)).1 0 = 0 := by
      rw [Work.ORHughesFree.SkewLaurentSeries.sub_apply, mono_apply, if_pos rfl, sub_self]
    simpa using VanishesBelow.succ hx0 hc
  -- the second factor `1 + a⁻¹·t⁰·x` is a unit
  have hy : VanishesBelow (mono (0 : ℤ) ((u⁻¹ : Aˣ) : A) * (f - mono 0 (f.1 0))) 1 := by
    have := VanishesBelow.mul (mono_vanishesBelow (0 : ℤ) ((u⁻¹ : Aˣ) : A) le_rfl) hx1
    simpa using this
  -- `a·t⁰ · a⁻¹·t⁰ = 1`
  have hmono : mono (0 : ℤ) ((u : Aˣ) : A) * mono (0 : ℤ) ((u⁻¹ : Aˣ) : A) = 1 := by
    rw [mono_mul]
    simp [mono_zero_one]
  -- so `f` factors as a product of two units
  have hsplit : mono 0 ((u : Aˣ) : A) *
      (1 + mono 0 ((u⁻¹ : Aˣ) : A) * (f - mono 0 (f.1 0))) = f := by
    rw [_root_.mul_add, _root_.mul_one, ← _root_.mul_assoc, hmono, _root_.one_mul]
    rw [show (f - mono 0 (f.1 0)) = f - mono 0 ((u : Aˣ) : A) from by rw [← hu_eq]]
    abel
  rw [← hsplit]
  exact IsUnit.mul (isUnit_mono_of_isUnit 0 (Units.isUnit u))
    (isUnit_one_add_of_vanishesBelow_one hy)

/-- **A series of order `m` with a unit `m`-th coefficient is a unit.**

Write `f = tᵐ · shift m f` (`mono_mul_shift`).  The shifted series `shift m f` vanishes below `0`
and its constant coefficient is `(-m) • f.1 m`, the image of the unit `f.1 m` under the ring
automorphism `(-m) • ·`, hence a unit; so `shift m f` is a unit by
`isUnit_of_vanishesBelow_zero_of_coeff_isUnit`, and `tᵐ = mono m 1` is a unit. -/
theorem isUnit_of_vanishesBelow_of_coeff_isUnit {f : SkewLaurentSeries A} {m : ℤ}
    (hm : VanishesBelow f m) (hu : IsUnit (f.1 m)) : IsUnit f := by
  have hshift : IsUnit (shift m f) := by
    apply isUnit_of_vanishesBelow_zero_of_coeff_isUnit hm.shift
    have h0 : (shift m f).1 0 = (Multiplicative.ofAdd (-m)) • f.1 m := by
      rw [shift_apply, _root_.add_zero]
    rw [h0]
    simpa [MulSemiringAction.toRingHom_apply] using
      hu.map (MulSemiringAction.toRingHom (Multiplicative ℤ) A (Multiplicative.ofAdd (-m)))
  rw [← mono_mul_shift m f]
  exact IsUnit.mul (isUnit_mono_of_isUnit m isUnit_one) hshift

/-- **The order of an inverse.**  If `f` vanishes below `m` and `f.1 m` is a unit of `A`, then any
two-sided inverse `g` (here only `g * f = 1` is used) vanishes below `-m`.

Suppose not, and let `k₀` be the least index with `g.1 k₀ ≠ 0` (`exists_least_nonzero_coeff`).
By `mul_apply_leading` the coefficient of degree `k₀ + m` of `g * f = 1` is the single product
`g.1 k₀ * (k₀ • f.1 m)`, whose second factor is a unit; so the product vanishes only if
`g.1 k₀ = 0`, which forces `k₀ + m = 0`. -/
theorem vanishesBelow_of_mul_eq_one {f g : SkewLaurentSeries A} {m : ℤ}
    (hf : VanishesBelow f m) (hu : IsUnit (f.1 m)) (hgf : g * f = 1) :
    VanishesBelow g (-m) := by
  by_contra hc
  simp only [VanishesBelow, not_forall] at hc
  obtain ⟨n, hn_lt, hn_ne⟩ := hc
  have hg_ne : g ≠ 0 := fun h0 => hn_ne (by rw [h0]; rfl)
  obtain ⟨k₀, hk₀, hk₀v⟩ := exists_least_nonzero_coeff g hg_ne
  have hlead := mul_apply_leading hk₀v hf
  have h1 : (g * f).1 (k₀ + m) = (if k₀ + m = 0 then (1 : A) else 0) := by
    rw [hgf, one_apply]
  have hk0 : k₀ = -m := by
    by_contra hne
    have hzero : g.1 k₀ * (Multiplicative.ofAdd k₀ • f.1 m) = 0 := by
      rw [← hlead, h1, if_neg (by omega)]
    have hs : IsUnit ((Multiplicative.ofAdd k₀) • f.1 m) := by
      simpa [MulSemiringAction.toRingHom_apply] using
        hu.map (MulSemiringAction.toRingHom (Multiplicative ℤ) A (Multiplicative.ofAdd k₀))
    exact hk₀ ((IsUnit.mul_left_eq_zero hs).mp hzero)
  exact hn_ne (hk₀v n (by omega))

theorem exists_inverse_of_vanishesBelow_of_coeff_isUnit {A : Type} [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A]
    {f : Work.ORHughesFree.SkewLaurentSeries A} {m : ℤ}
    (hm : Work.ORHughesFree.SkewLaurentSeries.VanishesBelow f m) (hu : IsUnit (f.1 m)) :
    ∃ g : Work.ORHughesFree.SkewLaurentSeries A, f * g = 1 ∧ g * f = 1 ∧
      Work.ORHughesFree.SkewLaurentSeries.VanishesBelow g (-m) := by
  obtain ⟨u, hu_eq⟩ := isUnit_of_vanishesBelow_of_coeff_isUnit hm hu
  refine ⟨↑(u⁻¹), ?_, ?_, ?_⟩
  · rw [← hu_eq, Units.mul_inv]
  · rw [← hu_eq, Units.inv_mul]
  · exact vanishesBelow_of_mul_eq_one (g := ↑(u⁻¹)) hm hu (by rw [← hu_eq, Units.inv_mul])

end Work.ORHughesFree.SkewLaurentSeries
