import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

/-- **Huppert V.7.1.** An average of `d` roots of unity, all of order dividing `M`, which is an algebraic integer is either `0` or has modulus `1`.

Proof strategy: put `K := ℚ(ζ)` for a primitive `M`-th root of unity `ζ ∈ ℂ` (`IntermediateField`
of `ℂ`), a number field containing `z` (each element of `s` is `ζ ^ k`).  For every
`σ : K →ₐ[ℚ] ℂ`, `σ ζ` is again an `M`-th root of unity, so `σ` sends every element of `s` to a
complex number of modulus `1`, whence `‖σ z‖ ≤ 1`.  `Algebra.norm_eq_prod_embeddings` writes
`Algebra.norm ℚ z` (as an element of `ℂ`) as the product of the `σ z`; that norm is a nonzero
integer (integral element of `ℚ`), so it has modulus `≥ 1`, forcing every `‖σ z‖ = 1`, in
particular `‖z‖ = 1` for the inclusion embedding. -/
theorem avg_rootsOfUnity_integral {z : ℂ} {d M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (hint : IsIntegral ℤ z)
    (h : ∃ s : Multiset ℂ, s.card = d ∧ (∀ x ∈ s, x ^ M = 1) ∧ s.sum = (d : ℂ) * z) :
    z = 0 ∨ ‖z‖ = 1 := by sorry

end Work.CharCore
