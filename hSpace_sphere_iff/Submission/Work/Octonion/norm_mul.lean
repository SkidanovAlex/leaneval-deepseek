/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team
-/
import Mathlib
import Submission.Work.Octonion.Basic

/-!
# The octonion norm is multiplicative

`Submission.Octonion` is the Cayley–Dickson double of the quaternions `ℍ = ℍ[ℝ]`, equipped with
the `ℓ²` norm `‖(a,b)‖² = ‖a‖² + ‖b‖²` and the product
`(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)`.

This file proves that this norm is multiplicative, `‖x * y‖ = ‖x‖ * ‖y‖`, i.e. that `𝕆` is a
composition algebra (in the sense of Hurwitz).  Together with `norm_one`, `one_mul`, `mul_one` and
`continuous_mul` this makes the unit sphere `S⁷` of `𝕆` an H-space.

The proof is the classical Cayley–Dickson computation: writing `x = (a, b)`, `y = (c, d)` one has

`‖x * y‖² = ‖a*c - star d * b‖² + ‖d*a + b*star c‖²`

and expanding both squares with the real inner product on `ℍ` (where `⟪u,v⟫ = (u * star v).re`,
so that `⟪u,v⟫ = (u * star v).re`) the two cross terms are
`-2 * ⟪a*c, star d * b⟫` and `+2 * ⟪d*a, b*star c⟫`, which are equal because the real part of a
product of quaternions is invariant under cyclic permutation of the factors
(`(u*v*w*z).re = (z*u*v*w).re`).  The four remaining terms give exactly
`(‖a‖² + ‖b‖²) * (‖c‖² + ‖d‖²) = ‖x‖² * ‖y‖²` by multiplicativity of the quaternion norm.
-/

open scoped Quaternion

namespace Work.Octonion

open Submission

/-- The real part of a product of quaternions is invariant under swapping the two factors. -/
theorem NormMul.re_mul_comm (a b : ℍ) : (a * b).re = (b * a).re := by
  rw [Quaternion.re_mul, Quaternion.re_mul]; ring

/-- The real part of a product of four quaternions is invariant under cyclic permutation,
`(a * b * c * d).re = (d * a * b * c).re`. -/
theorem NormMul.re_mul_four (a b c d : ℍ) : (a * b * c * d).re = (d * a * b * c).re := by
  have h : ((a * b * c) * d).re = (d * (a * b * c)).re := NormMul.re_mul_comm _ _
  simpa only [mul_assoc] using h

/-- `star (star x * y) = star y * x` for quaternions. -/
theorem NormMul.star_star_mul (x y : ℍ) : star (star x * y) = star y * x := by
  rw [star_mul, star_star]

/-- `star (x * star y) = y * star x` for quaternions. -/
theorem NormMul.star_mul_star (x y : ℍ) : star (x * star y) = y * star x := by
  rw [star_mul, star_star]

/-- The two cross terms in the Cayley–Dickson computation are equal:

`⟪a * c, star d * b⟫ = ⟪d * a, b * star c⟫`.

Both sides have real part `(a * c * star b * d).re`, by cyclicity of the real part of a product of
four quaternions. -/
theorem NormMul.inner_cross (a b c d : ℍ) :
    inner ℝ (a * c) (star d * b) = inner ℝ (d * a) (b * star c) := by
  rw [Quaternion.inner_def, Quaternion.inner_def, NormMul.star_star_mul,
    NormMul.star_mul_star]
  simpa only [mul_assoc] using NormMul.re_mul_four a c (star b) d

/-- The Cayley–Dickson norm computation for quaternions `a b c d`:
`‖a*c - star d * b‖² + ‖d*a + b*star c‖² = (‖a‖² + ‖b‖²) * (‖c‖² + ‖d‖²)`. -/
theorem NormMul.norm_sq_cd (a b c d : ℍ) :
    ‖a * c - star d * b‖ ^ 2 + ‖d * a + b * star c‖ ^ 2
      = (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  rw [norm_sub_sq_real, norm_add_sq_real]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  rw [Quaternion.norm_star, Quaternion.norm_star]
  rw [NormMul.inner_cross]
  ring

/-- The first component of a product of octonions. -/
theorem NormMul.fst_mul (x y : Octonion) :
    (x * y).fst = x.fst * y.fst - star y.snd * x.snd := by
  show (WithLp.ofLp (x * y)).1 = _
  rw [Octonion.ofLp_mul]
  rfl

/-- The second component of a product of octonions. -/
theorem NormMul.snd_mul (x y : Octonion) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := by
  show (WithLp.ofLp (x * y)).2 = _
  rw [Octonion.ofLp_mul]
  rfl

/-- **The octonion norm is multiplicative**: `‖x * y‖ = ‖x‖ * ‖y‖`.

This is the statement that `𝕆` is a composition algebra, i.e. that the Cayley–Dickson double of
the quaternions inherits the multiplicative norm. -/
theorem norm_mul (x y : Submission.Octonion) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  have h1 : ‖x * y‖ ^ 2 = (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) * (‖y.fst‖ ^ 2 + ‖y.snd‖ ^ 2) := by
    rw [Octonion.norm_sq_eq, NormMul.fst_mul, NormMul.snd_mul]
    exact NormMul.norm_sq_cd x.fst x.snd y.fst y.snd
  have h2 : (‖x‖ * ‖y‖) ^ 2 = (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) *
      (‖y.fst‖ ^ 2 + ‖y.snd‖ ^ 2) := by
    rw [mul_pow, Octonion.norm_sq_eq, Octonion.norm_sq_eq]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    (h1.trans h2.symm)

end Work.Octonion
