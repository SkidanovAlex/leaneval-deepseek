import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `A(K,θ)` has exponent `4`, and so does anything isomorphic to it

Higman's group `A(K,θ)` is `K × K` with `(a,b) * (c,d) = (a+c, b+d+a·θ c)`.  Over a field
of characteristic two the first coordinate of a square vanishes and the second collapses:
`x * x = ⟨0, a·θ a⟩`.  Hence `x ^ 4 = (x ^ 2) ^ 2 = ⟨0, c⟩ * ⟨0, c⟩ = 1` because `1 + 1 = 0`
in `K`.  No hypothesis on `θ` is needed beyond it being a ring automorphism.

Consequently any group `Q` isomorphic to `A(K,θ)` has exponent dividing `4`:
`Work.ZassenhausSuzuki.pow_four_of_mulEquiv`, transported through the isomorphism.
-/

set_option autoImplicit false

namespace Work.ZassenhausSuzuki

namespace SzA

variable {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)

/-- In characteristic two the square of an element of `A(K,θ)` is `⟨0, a·θa⟩`: both
`x.a + x.a` and `x.b + x.b` vanish. -/
theorem mul_self_eq (x : SzA K θ) : x * x = (⟨0, x.a * θ x.a⟩ : SzA K θ) := by
  ext <;> simp [CharTwo.add_self_eq_zero]

/-- **`A(K,θ)` has exponent dividing `4`.**  Every element of Higman's group over a field of
characteristic two satisfies `x ^ 4 = 1`. -/
theorem pow_four_eq_one (x : SzA K θ) : x ^ 4 = 1 := by
  have h2 : x ^ 2 = (⟨0, x.a * θ x.a⟩ : SzA K θ) := by
    rw [pow_two]; exact mul_self_eq θ x
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, pow_two]
  ext <;> simp [CharTwo.add_self_eq_zero]

end SzA

/-- Every element of a group isomorphic to Higman's group `A(K,θ)` over a field of
characteristic two has order dividing `4`. -/
theorem pow_four_of_mulEquiv {Q : Type*} [Group Q] {K : Type*} [Field K] [CharP K 2]
    (θ : K ≃+* K) (e : Q ≃* Work.ZassenhausSuzuki.SzA K θ) : ∀ x : Q, x ^ 4 = 1 := by
  intro x
  refine e.injective ?_
  rw [map_pow, SzA.pow_four_eq_one θ, map_one]

end Work.ZassenhausSuzuki
