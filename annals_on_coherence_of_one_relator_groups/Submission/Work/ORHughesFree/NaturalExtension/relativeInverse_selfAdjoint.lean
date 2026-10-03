/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Relative inverses of self-adjoint elements, and the formula `x^{[-1]} = (x∗ x)^{[-1]} x∗`

This file collects the elementary facts about relative (Moore--Penrose) inverses in a `∗`-regular
ring that are needed for the epicity of the `∗`-regular closure ([Jaikin, *The base change in the
Atiyah and the Lück approximation conjectures*, GAFA 29 (2019), Proposition 3.2(6), (7)]):

* the relative inverse of a self-adjoint element is self-adjoint
  (`star_eq_self_of_isRelativeInverse_selfAdjoint`),
* a self-adjoint element commutes with its relative inverse
  (`mul_comm_of_isRelativeInverse_selfAdjoint`),
* the relative inverse of `x` is `(x∗ x)^{[-1]} x∗` (`isRelativeInverse_mul_star`).

The last one is the key structural fact: it shows that *arbitrary* relative inverses are generated
from relative inverses of *self-adjoint* elements together with the ring operations.
-/
import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.isRelativeInverse_unique
import Submission.Work.ORHughesFree.StarRegular.exists_isRelativeInverse

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

open Work.ORHughesFree

/-! ## The star of a relative inverse -/

/-- The star of a relative (Moore--Penrose) inverse is the relative inverse of the star. -/
theorem isRelativeInverse_star_of {U : Type*} [Ring U] [StarRing U] {x y : U}
    (h : IsRelativeInverse x y) : IsRelativeInverse (star x) (star y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : star (x * y * x) = star x := by rw [h.left]
    simpa [star_mul, mul_assoc] using h1
  · have h1 : star (y * x * y) = star y := by rw [h.right]
    simpa [star_mul, mul_assoc] using h1
  · show star (star x * star y) = star x * star y
    rw [star_mul, star_star, star_star]
    rw [show star x * star y = y * x by rw [← star_mul, h.star_right]]
  · show star (star y * star x) = star y * star x
    rw [star_mul, star_star, star_star]
    rw [show star y * star x = x * y by rw [← star_mul, h.star_left]]

/-! ## Self-adjoint elements and their relative inverses -/

/-- **The relative inverse of a self-adjoint element is self-adjoint**
([Jaikin, GAFA 2019, Proposition 3.2(5)]).

Indeed, if `y = y∗` then by `isRelativeInverse_star_of` the element `w∗` is again a relative
inverse of `y = y∗`, so `w∗ = w` by uniqueness of the relative inverse. -/
theorem star_eq_self_of_isRelativeInverse_selfAdjoint {U : Type*} [Ring U] [StarRing U] {y w : U}
    (hy : star y = y) (hw : IsRelativeInverse y w) : star w = w := by
  have h1 : IsRelativeInverse y (star w) := by
    have := isRelativeInverse_star_of hw
    rwa [hy] at this
  exact StarRegular.isRelativeInverse_unique h1 hw

/-- **A self-adjoint element commutes with its relative inverse**
([Jaikin, GAFA 2019, Proposition 3.2(7)]).

By definition `y ∗ w` is self-adjoint, i.e. `w∗ ∗ y∗ = y ∗ w`; since `y∗ = y` and `w∗ = w` this
reads `w ∗ y = y ∗ w`. -/
theorem mul_comm_of_isRelativeInverse_selfAdjoint {U : Type*} [Ring U] [StarRing U] {y w : U}
    (hy : star y = y) (hw : IsRelativeInverse y w) : w * y = y * w := by
  have hws : star w = w := star_eq_self_of_isRelativeInverse_selfAdjoint hy hw
  have h := hw.star_left
  rw [star_mul, hy, hws] at h
  exact h

/-! ## The formula `x^{[-1]} = (x∗ x)^{[-1]} x∗` -/

/-- **The relative inverse of `x` is `(x∗ x)^{[-1]} x∗`**
([Jaikin, GAFA 2019, Proposition 3.2(6)]).

Let `s = x∗ x` and let `v` be the relative inverse of `s`.  We verify that `v ∗ x∗` satisfies the
four defining properties of the relative inverse of `x`; by uniqueness
(`StarRegular.isRelativeInverse_unique`) this exhibits the relative inverse of `x`.

The only non-formal point is the first property `x (v x∗) x = x`: writing `s = x∗ x` and using
`s v s = s` together with `v∗ = v` we get
`(x v s - x)∗ (x v s - x) = svx∗ · xvs - svx∗ · x - x∗ · xvs + x∗x = s - s - s + s = 0`,
so `x v s = x` by properness of the involution. -/
theorem isRelativeInverse_mul_star {U : Type*} [Ring U] [StarRing U] [IsStarRegular U]
    {x v : U} (hv : IsRelativeInverse (star x * x) v) :
    IsRelativeInverse x (v * star x) := by
  have hsfix : star (star x * x) = star x * x := by rw [star_mul, star_star]
  have hvs : star v = v := star_eq_self_of_isRelativeInverse_selfAdjoint hsfix hv
  have hsvs : (star x * x) * v * (star x * x) = star x * x := hv.left
  have hvsv : v * (star x * x) * v = v := hv.right
  have hstar : star (star x * x) = star x * x := hsfix
  -- the first defining property
  have hxa : x * v * (star x * x) = x := by
    refine sub_eq_zero.mp (IsStarRegular.proper (x * v * (star x * x) - x) ?_)
    have hst : star (x * v * (star x * x)) = (star x * x) * (v * star x) := by
      rw [star_mul, star_mul, star_mul, star_star, hvs]
    rw [star_sub, hst]
    have hexp : ((star x * x) * (v * star x) - star x) * (x * v * (star x * x) - x)
        = ((star x * x) * v * star x) * (x * v * (star x * x))
          - ((star x * x) * v * star x) * x
          - star x * (x * v * (star x * x)) + star x * x := by
      noncomm_ring
    rw [hexp]
    have t1 : ((star x * x) * v * star x) * (x * v * (star x * x)) = star x * x := by
      have h : ((star x * x) * v * star x) * (x * v * (star x * x))
          = (star x * x) * v * ((star x * x) * v * (star x * x)) := by noncomm_ring
      rw [h, hsvs, hsvs]
    have t2 : ((star x * x) * v * star x) * x = star x * x := by
      have h : ((star x * x) * v * star x) * x = (star x * x) * v * (star x * x) := by
        noncomm_ring
      rw [h, hsvs]
    have t3 : star x * (x * v * (star x * x)) = star x * x := by
      have h : star x * (x * v * (star x * x)) = (star x * x) * v * (star x * x) := by
        noncomm_ring
      rw [h, hsvs]
    rw [t1, t2, t3]
    abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `x (v x∗) x = x`
    have h : x * (v * star x) * x = x * v * (star x * x) := by noncomm_ring
    rw [h, hxa]
  · -- `(v x∗) x (v x∗) = v x∗`
    have h : (v * star x) * x * (v * star x) = (v * (star x * x) * v) * star x := by
      noncomm_ring
    rw [h, hvsv]
  · -- `x (v x∗)` is self-adjoint
    rw [star_mul, star_mul, star_star, hvs, mul_assoc]
  · -- `(v x∗) x` is self-adjoint
    have hcomm : v * (star x * x) = (star x * x) * v :=
      mul_comm_of_isRelativeInverse_selfAdjoint hsfix hv
    rw [star_mul, star_mul, star_star, hvs, ← mul_assoc, mul_assoc v (star x) x, ← hcomm]

end Work.ORHughesFree.NaturalExtension
