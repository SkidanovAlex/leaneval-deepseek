/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Mathlib
import Submission.NK.Chebotarev.QuadraticGaussSumInCyclotomic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `p` is a square in a field containing `i` and a primitive `p`-th root of unity

For an odd prime `p`, any field `F` of characteristic `0` that contains both a primitive
`p`-th root of unity `ζ` and a square root `i` of `-1` contains a square root of `p`.

The arithmetic content is the quadratic Gauss sum, already established in
`NK.Chebotarev.QuadraticGaussSumInCyclotomic`: the Gauss sum
`g = ∑ a, (a/p) ζ^a` satisfies `g ^ 2 = (if p % 4 = 1 then 1 else -1) * p`.

* If `p ≡ 1 (mod 4)` then `g ^ 2 = p`;
* if `p ≡ 3 (mod 4)` then `g ^ 2 = -p`, and since `i ^ 2 = -1` we get
  `(g * i) ^ 2 = g ^ 2 * i ^ 2 = (-p) * (-1) = p`.

This is the classical statement that the quadratic subfield of `ℚ(ζ_p)` is `ℚ(√(p*))` with
`p* = (-1)^((p-1)/2) p`, combined with the fact that adjoining `i` removes the sign.
-/

namespace NK.Chebotarev

theorem ExistsSqEqPrimeOfPrimitiveRoot {F : Type*} [Field F] [Algebra ℚ F] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {i : F} (hi : i ^ 2 = -1) : ∃ x : F, x ^ 2 = (p : F) := by
  -- the quadratic Gauss sum: a square root of `(if p % 4 = 1 then 1 else -1) * p`
  obtain ⟨y, hy⟩ := QuadraticGaussSumInCyclotomic p hp ζ hζ
  by_cases h : p % 4 = 1
  · -- `p ≡ 1 (mod 4)`: the Gauss sum itself is the required square root
    refine ⟨y, ?_⟩
    rw [hy, if_pos h]
    simp
  · -- `p ≡ 3 (mod 4)`: `y ^ 2 = -p`, so `y * i` squares to `p`
    refine ⟨y * i, ?_⟩
    rw [mul_pow, hy, hi, if_neg h]
    push_cast
    ring

end NK.Chebotarev
