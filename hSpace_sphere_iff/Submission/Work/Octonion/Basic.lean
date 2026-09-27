/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The octonions

Mathlib has no octonions.  This file begins the construction of the octonion algebra `𝕆` as the
Cayley–Dickson double of the quaternions `ℍ`, equipped with the `ℓ²`-norm on `ℍ × ℍ` (so that
the unit sphere of `𝕆` is the Euclidean sphere `S⁷`).

The type is `WithLp 2 (ℍ × ℍ)`, i.e. `ℍ × ℍ` with the norm `‖(a,b)‖ = √(‖a‖² + ‖b‖²)`.  The
multiplication is the Cayley–Dickson product
`(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)`,
which is `ℝ`-bilinear, has `(1, 0)` as a strict two-sided unit and satisfies
`‖x * y‖ = ‖x‖ * ‖y‖` (the latter is proved in `Submission/Work/Octonion/NormMul.lean`).

The octonion algebra is neither associative nor commutative, but its unit sphere is an H-space;
this is the input for the `n = 7` case of Adams' theorem.
-/
import Mathlib

open scoped Quaternion
open WithLp

namespace Submission

/-- The octonions, as the Cayley–Dickson double of the quaternions with the `ℓ²` norm. -/
abbrev Octonion : Type := WithLp 2 (ℍ × ℍ)

namespace Octonion

/-- The Cayley–Dickson product on `ℍ × ℍ`. -/
noncomputable def cdMul (x y : ℍ × ℍ) : ℍ × ℍ :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)

noncomputable instance : Mul Octonion :=
  ⟨fun x y => WithLp.toLp 2 (cdMul (WithLp.ofLp x) (WithLp.ofLp y))⟩

noncomputable instance : One Octonion := ⟨WithLp.toLp 2 (1, 0)⟩

/-- The underlying pair of a product is the Cayley–Dickson product of the underlying pairs. -/
@[simp] theorem ofLp_mul (x y : Octonion) :
    WithLp.ofLp (x * y) = cdMul (WithLp.ofLp x) (WithLp.ofLp y) := rfl

/-- The underlying pair of `1`. -/
@[simp] theorem ofLp_one : WithLp.ofLp (1 : Octonion) = (1, 0) := rfl

/-- The first quaternionic component of an octonion. -/
noncomputable abbrev fst (x : Octonion) : ℍ := (WithLp.ofLp x).1

/-- The second quaternionic component of an octonion. -/
noncomputable abbrev snd (x : Octonion) : ℍ := (WithLp.ofLp x).2

@[simp] theorem ofLp_mk (a b : ℍ) : WithLp.ofLp (WithLp.toLp 2 (a, b) : Octonion) = (a, b) := rfl

@[simp] theorem fst_mk (a b : ℍ) : (WithLp.toLp 2 (a, b) : Octonion).fst = a := rfl

@[simp] theorem snd_mk (a b : ℍ) : (WithLp.toLp 2 (a, b) : Octonion).snd = b := rfl

/-- The norm identity defining the octonion norm on `ℍ × ℍ`. -/
theorem norm_sq_eq (x : Octonion) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 x

end Octonion

end Submission
