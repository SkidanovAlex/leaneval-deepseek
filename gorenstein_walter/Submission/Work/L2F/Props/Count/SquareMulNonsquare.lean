/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The nonsquares of a finite field form a single coset of the squares

In a finite field `F` (with `2 ≠ 0`, so that the squaring map is not a bijection), the
product of two nonsquares is a square.  Concretely, given nonsquares `d` and `μ` there is a
`c` with `d * c ^ 2 = μ`: this says that the set of nonsquares is a coset of the subgroup of
nonzero squares in `Fˣ`, i.e. that `μ / d` is a square.

The proof uses Mathlib's quadratic character `quadraticChar F : MulChar F ℤ`, which takes the
value `-1` exactly on the nonsquares and is multiplicative.  Hence
`quadraticChar F (d * μ) = (-1) * (-1) = 1`, so `d * μ` is a (nonzero) square, say `y * y`.
Then `c = y / d` satisfies `d * c ^ 2 = d * (y ^ 2 / d ^ 2) = y ^ 2 / d = (d * μ) / d = μ`.

(When `2 = 0` the squaring map `x ↦ x ^ 2` is injective, hence surjective, and there are no
nonsquares at all; the statement is then vacuous.  So the hypothesis `2 ≠ 0` is not logically
needed, only faithful to the intended setting of odd characteristic.)
-/
import Mathlib

namespace Work.L2F.Props.Count

theorem SquareMulNonsquare (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    {d μ : F} (hd : ¬ IsSquare d) (hμ : ¬ IsSquare μ) :
    ∃ c : F, d * (c * c) = μ := by
  classical
  -- `0` is a square, so nonsquares are nonzero
  have hd0 : d ≠ 0 := by rintro rfl; exact hd IsSquare.zero
  have hμ0 : μ ≠ 0 := by rintro rfl; exact hμ IsSquare.zero
  -- the quadratic character is `-1` on nonsquares and multiplicative
  have hd1 : quadraticChar F d = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hd
  have hμ1 : quadraticChar F μ = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hμ
  have hsq : IsSquare (d * μ) := by
    rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hd0 hμ0), map_mul, hd1, hμ1]
    norm_num
  obtain ⟨y, hy⟩ := hsq
  -- `hy : d * μ = y * y`; take `c = y / d`
  exact ⟨y * d⁻¹, by
    rw [show y * d⁻¹ * (y * d⁻¹) = y * y * (d⁻¹ * d⁻¹) by ring, ← hy]
    field_simp⟩

end Work.L2F.Props.Count
