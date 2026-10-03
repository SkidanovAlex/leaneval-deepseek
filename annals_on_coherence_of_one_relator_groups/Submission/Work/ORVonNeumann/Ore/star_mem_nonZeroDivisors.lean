/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The non-zero-divisors of a `*`-ring are `*`-stable

The set of (two-sided) non-zero-divisors of a `*`-ring is invariant under the involution, so it
is a `*`-invariant Ore set whenever it is an Ore set.  This is the hypothesis `hS` of the
involution on the Ore localisation
(`Work.ORVonNeumann.Ore.star_oreLocalization`); for `N(G)` it makes `U(G) = N(G)[(nzd)⁻¹]`
a `*`-ring.

## Main result

* `Work.ORVonNeumann.Ore.star_mem_nonZeroDivisors` —
  `a ∈ nonZeroDivisors R → a⋆ ∈ nonZeroDivisors R`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.ORVonNeumann.Ore

/-- The `*`-image of a (two-sided) non-zero-divisor is again a non-zero-divisor. -/
theorem star_mem_nonZeroDivisors {R : Type*} [Ring R] [StarRing R] {a : R}
    (ha : a ∈ nonZeroDivisors R) : star a ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff] at ha ⊢
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h1 : star x * a = 0 := by
      have h : star (star x * a) = 0 := by
        rw [star_mul, star_star]
        exact hx
      have := congrArg star h
      simpa using this
    exact star_eq_zero.mp (ha.2 (star x) h1)
  · have h1 : a * star x = 0 := by
      have h : star (a * star x) = 0 := by
        rw [star_mul, star_star]
        exact hx
      have := congrArg star h
      simpa using this
    exact star_eq_zero.mp (ha.1 (star x) h1)

end Work.ORVonNeumann.Ore
