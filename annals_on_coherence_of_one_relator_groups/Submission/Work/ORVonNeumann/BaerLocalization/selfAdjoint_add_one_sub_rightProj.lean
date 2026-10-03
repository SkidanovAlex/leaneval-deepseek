/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The self-adjoint element `a + (1 - rightProj h a)` of a Baer `*`-ring

Let `R` be an element-Baer `*`-ring (`Work.ORVonNeumann.BaerRing.HasBaerAnnihilators`), let
`a : R` be self-adjoint (`star a = a`) and put `p := rightProj h a`, the right projection of
`a`.  This file proves the four multiplicative identities of `b := a + (1 - p)` together with
the fact that `b` is a non-zero-divisor:

* `b * a = a * a` and `a * b = a * a` (`b` behaves like `a` against `a`);
* `b * p = a` and `p * b = a` (`b` carries the source projection `p` to `a`);
* `b ∈ nonZeroDivisors R`.

These are exactly the ring-theoretic hypotheses under which the conjugation identity
`g g^{[-1]} g = g` for `g = b⁻¹ * a` becomes available, i.e. the core of the passage from a
Baer `*`-ring to the `*`-regular Ore localisation at its non-zero-divisors.

The proof rests on two basic properties of `rightProj h a` (see `BaerRing`):
`a * rightProj h a = a` always, and `rightProj h a * a = a` as well when `a` is self-adjoint
(the left-handed companion of `rightProj_mul_self`).  Writing `e := 1 - rightProj h a`, so that
`e` is again a star projection with `a * e = 0`, `e * a = 0` and `(a + e) * e = e`, all five
claims are then direct computations; the non-zero-divisor property follows because
`b * x = 0` forces `a * x = 0`, whence `x = e * y` and then `x = (b * e) * y = b * x = 0`,
while `x * b = 0` first gives `x * e = 0`, then `x * a = 0`, and starring produces
`x = y * e = (x * e) * e = 0`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.BaerLocalization.BaerRing

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORVonNeumann.BaerLocalization

open Work.ORVonNeumann.BaerRing

theorem selfAdjoint_add_one_sub_rightProj {R : Type*} [Ring R] [StarRing R] (h : Work.ORVonNeumann.BaerRing.HasBaerAnnihilators R) {a : R} (ha : star a = a) : (a + (1 - Work.ORVonNeumann.BaerRing.rightProj h a)) * a = a * a ∧ a * (a + (1 - Work.ORVonNeumann.BaerRing.rightProj h a)) = a * a ∧ (a + (1 - Work.ORVonNeumann.BaerRing.rightProj h a)) * Work.ORVonNeumann.BaerRing.rightProj h a = a ∧ Work.ORVonNeumann.BaerRing.rightProj h a * (a + (1 - Work.ORVonNeumann.BaerRing.rightProj h a)) = a ∧ a + (1 - Work.ORVonNeumann.BaerRing.rightProj h a) ∈ nonZeroDivisors R := by
  -- `e := 1 - p` is a star projection, hence idempotent and self-adjoint.
  have he : star (1 - rightProj h a) = 1 - rightProj h a :=
    (rightProj_isStarProjection h a).one_sub.isSelfAdjoint.star_eq
  have hp : rightProj h a * rightProj h a = rightProj h a :=
    (rightProj_isStarProjection h a).isIdempotentElem.eq
  have hee : (1 - rightProj h a) * (1 - rightProj h a) = 1 - rightProj h a :=
    (rightProj_isStarProjection h a).one_sub.isIdempotentElem.eq
  -- The two basic identities: `a * p = a` and, as `a` is self-adjoint, `p * a = a`.
  have hae : a * (1 - rightProj h a) = 0 := mul_one_sub_rightProj_eq_zero h a
  have hap : a * rightProj h a = a := rightProj_mul_self h a
  have hpa : rightProj h a * a = a := by
    have h1 : (1 - rightProj h a) * a = 0 := by
      have h0 := congrArg star (mul_one_sub_rightProj_eq_zero h a)
      rw [star_mul, star_zero, ha, he] at h0
      exact h0
    have h2 : (1 - rightProj h a) * a = a - rightProj h a * a := by rw [sub_mul, one_mul]
    rw [h2, sub_eq_zero] at h1
    exact h1.symm
  have hea : (1 - rightProj h a) * a = 0 := by rw [sub_mul, one_mul, hpa, sub_self]
  -- Orthogonality of `p` and `e`.
  have hpe : rightProj h a * (1 - rightProj h a) = 0 := by
    rw [mul_sub, mul_one, hp, sub_self]
  have hep : (1 - rightProj h a) * rightProj h a = 0 := by
    rw [sub_mul, one_mul, hp, sub_self]
  -- The action of `b := a + e` on `e`, `p` and `a`.
  have hbe : (a + (1 - rightProj h a)) * (1 - rightProj h a) = 1 - rightProj h a := by
    rw [add_mul, hae, hee, zero_add]
  have hpb : rightProj h a * (a + (1 - rightProj h a)) = a := by
    rw [mul_add, hpa, hpe, add_zero]
  have hbp : (a + (1 - rightProj h a)) * rightProj h a = a := by
    rw [add_mul, hap, hep, add_zero]
  refine ⟨?_, ?_, hbp, hpb, ?_⟩
  · rw [add_mul, hea, add_zero]
  · rw [mul_add, hae, add_zero]
  · rw [mem_nonZeroDivisors_iff]
    refine ⟨?_, ?_⟩
    · -- `b * x = 0 → x = 0`.
      intro x hx
      have hax : a * x = 0 := by
        calc a * x = (rightProj h a * (a + (1 - rightProj h a))) * x := by rw [hpb]
          _ = rightProj h a * ((a + (1 - rightProj h a)) * x) := by rw [mul_assoc]
          _ = rightProj h a * 0 := by rw [hx]
          _ = 0 := mul_zero _
      obtain ⟨y, hy⟩ := (rightProj_spec h a x).mp hax
      calc x = (1 - rightProj h a) * y := hy
        _ = ((a + (1 - rightProj h a)) * (1 - rightProj h a)) * y := by rw [hbe]
        _ = (a + (1 - rightProj h a)) * ((1 - rightProj h a) * y) := by rw [mul_assoc]
        _ = (a + (1 - rightProj h a)) * x := by rw [hy]
        _ = 0 := hx
    · -- `x * b = 0 → x = 0`.
      intro x hx
      have hxe : x * (1 - rightProj h a) = 0 := by
        calc x * (1 - rightProj h a)
            = x * ((a + (1 - rightProj h a)) * (1 - rightProj h a)) := by rw [hbe]
          _ = (x * (a + (1 - rightProj h a))) * (1 - rightProj h a) := by rw [← mul_assoc]
          _ = 0 * (1 - rightProj h a) := by rw [hx]
          _ = 0 := zero_mul _
      have hxa : x * a = 0 := by
        have h0 := hx
        rw [mul_add, hxe, add_zero] at h0
        exact h0
      have hax : a * star x = 0 := by
        have h0 := congrArg star hxa
        rw [star_mul, star_zero, ha] at h0
        exact h0
      obtain ⟨y, hy⟩ := (rightProj_spec h a (star x)).mp hax
      have hx_eq : x = star y * (1 - rightProj h a) := by
        calc x = star (star x) := (star_star x).symm
          _ = star ((1 - rightProj h a) * y) := by rw [hy]
          _ = star y * star (1 - rightProj h a) := star_mul _ _
          _ = star y * (1 - rightProj h a) := by rw [he]
      calc x = star y * (1 - rightProj h a) := hx_eq
        _ = (star y * (1 - rightProj h a)) * (1 - rightProj h a) := by rw [mul_assoc, hee]
        _ = x * (1 - rightProj h a) := by rw [hx_eq]
        _ = 0 := hxe

end Work.ORVonNeumann.BaerLocalization
