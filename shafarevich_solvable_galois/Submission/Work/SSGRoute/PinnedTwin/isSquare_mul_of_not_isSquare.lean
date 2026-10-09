/-
# The product of two non-squares in a finite field of odd characteristic is a square

In a finite field `κ` of characteristic `≠ 2`, the non-zero squares form a subgroup of
`κˣ` of index `2`; equivalently the quadratic character is a homomorphism onto `{±1}`,
so the product of two non-squares is a square.

This is proved here through Mathlib's description of the squaring behaviour of a finite
field of odd characteristic: for `a ≠ 0`, `a ^ (#κ / 2) = ±1`, and `a` is a square if and
only if that value is `1`.  Hence two non-squares both satisfy `a ^ (#κ / 2) = -1`, and
their product satisfies `(x * y) ^ (#κ / 2) = 1`.

## Main result

* `Work.SSGRoute.PinnedTwin.isSquare_mul_of_not_isSquare`
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PinnedTwin

/-- In a finite field `κ` of characteristic different from `2`, the product of two
elements that are not squares is a square. -/
theorem isSquare_mul_of_not_isSquare {κ : Type} [Field κ] [Fintype κ] (h2 : ringChar κ ≠ 2)
    {x y : κ} (hx : ¬ IsSquare x) (hy : ¬ IsSquare y) : IsSquare (x * y) := by
  -- `0` is always a square, so a non-square is non-zero.
  have hx0 : x ≠ 0 := fun h => hx (h.symm ▸ IsSquare.zero)
  have hy0 : y ≠ 0 := fun h => hy (h.symm ▸ IsSquare.zero)
  rw [FiniteField.isSquare_iff h2 (mul_ne_zero hx0 hy0)]
  -- A non-zero element of a finite field of odd characteristic has
  -- `a ^ (#κ / 2) = ±1`, and it is a square exactly when the value is `1`.
  have hxp : x ^ (Fintype.card κ / 2) = -1 := by
    rcases FiniteField.pow_dichotomy h2 hx0 with h | h
    · exact absurd ((FiniteField.isSquare_iff h2 hx0).mpr h) hx
    · exact h
  have hyp : y ^ (Fintype.card κ / 2) = -1 := by
    rcases FiniteField.pow_dichotomy h2 hy0 with h | h
    · exact absurd ((FiniteField.isSquare_iff h2 hy0).mpr h) hy
    · exact h
  rw [mul_pow, hxp, hyp, neg_mul_neg, one_mul]

end Work.SSGRoute.PinnedTwin
