import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The surjectivity of `λ ↦ λ · θ λ` on `Kˣ` (`θ` Tits)

This is the field-theoretic ingredient of the Suzuki partition of `A(K,θ)^#` (BG 5.16–5.17,
HB III XI 11.11): for a Tits endomorphism `θ` of a field `K` of characteristic two the map
`λ ↦ λ · θ(λ)` is onto `Kˣ`.

It is put in its own file (rather than in `suzukiCoordsProp`) so that it can be imported from
below as well: `frel_center_aux` uses it, and it must not depend on the (later) results of
`suzukiCoordsProp`.
-/

set_option autoImplicit false

namespace Work.ZassenhausSuzuki

/-- **`λ ↦ λ · θ λ` is surjective on `Kˣ`** when `θ` is a Tits endomorphism: the map
`μ ↦ θ μ · μ⁻¹` is a two-sided inverse, because `(λ^{1+θ})^{θ-1} = λ^{θ²-1} = λ^{2-1} = λ`. -/
theorem exists_unit_mul_theta {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K}
    (hθ : IsTitsTheta θ) (b : Kˣ) : ∃ lam : Kˣ, (lam : K) * θ (lam : K) = (b : K) := by
  have hb : (b : K) ≠ 0 := Units.ne_zero b
  have hθb : θ (b : K) ≠ 0 := θ.map_ne_zero_iff.mpr hb
  refine ⟨Units.mk0 (θ (b : K) * ((b : K))⁻¹) (mul_ne_zero hθb (inv_ne_zero hb)), ?_⟩
  show (θ (b : K) * ((b : K))⁻¹) * θ (θ (b : K) * ((b : K))⁻¹) = (b : K)
  rw [map_mul, map_inv₀, hθ.2 b]
  field_simp

end Work.ZassenhausSuzuki
