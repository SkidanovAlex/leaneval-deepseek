import Mathlib
import Submission.Work.Analysis.Interpolation.Basic

namespace Work.Analysis.Interpolation

/-- Arithmetic core of three-factor `rpow` interpolation.

For coefficients `m₀, m₁ ≥ 0`, points `x, y > 0` and exponents satisfying the two
interpolation relations `(1 - θ) α₀ + θ α₁ = 1`, `(1 - θ) β₀ + θ β₁ = 1`, the
`θ`-interpolated product of the two monomials `mᵢ x^{αᵢ} y^{βᵢ}` is the
`θ`-interpolated coefficient times `x * y`:

`(m₀ x^{α₀} y^{β₀}) ^ (1 - θ) * (m₁ x^{α₁} y^{β₁}) ^ θ = m₀ ^ (1 - θ) * m₁ ^ θ * x * y`.

The identity is the `rpow` bookkeeping behind the Stein interpolation step: `mul_rpow`
splits each monomial into its three factors, `rpow_mul` flattens the nested powers,
and `rpow_add` recombines the `x`-powers (resp. `y`-powers) into `x ^ 1` (resp. `y ^ 1`).
The hypotheses on the coefficients are `≤` — the identity also holds at `mᵢ = 0`,
where `Real.mul_rpow` (which only needs nonnegativity) is the relevant tool, so no
case split on vanishing coefficients is required. -/
lemma rpow_interp_arith {m₀ m₁ x y α₀ α₁ β₀ β₁ θ : ℝ} (hm₀ : 0 ≤ m₀) (hm₁ : 0 ≤ m₁) (hx : 0 < x) (hy : 0 < y) (hα : (1 - θ) * α₀ + θ * α₁ = 1) (hβ : (1 - θ) * β₀ + θ * β₁ = 1) : (m₀ * x ^ α₀ * y ^ β₀) ^ (1 - θ) * (m₁ * x ^ α₁ * y ^ β₁) ^ θ = m₀ ^ (1 - θ) * m₁ ^ θ * x * y := by
  have hxp : ∀ a : ℝ, 0 < x ^ a := fun a => Real.rpow_pos_of_pos hx a
  have hyp : ∀ a : ℝ, 0 < y ^ a := fun a => Real.rpow_pos_of_pos hy a
  -- split the monomial `m * x ^ a * y ^ b` raised to `c` into its three factors
  have key : ∀ (m a b c : ℝ), 0 ≤ m →
      (m * x ^ a * y ^ b) ^ c = m ^ c * x ^ (a * c) * y ^ (b * c) := by
    intro m a b c hm
    rw [Real.mul_rpow (mul_nonneg hm (hxp a).le) (hyp b).le,
      Real.mul_rpow hm (hxp a).le,
      ← Real.rpow_mul hx.le a c, ← Real.rpow_mul hy.le b c]
  -- the `x`-exponents recombine to `1`, hence the `x`-powers multiply to `x`
  have hxx : x ^ (α₀ * (1 - θ)) * x ^ (α₁ * θ) = x := by
    rw [← Real.rpow_add hx (α₀ * (1 - θ)) (α₁ * θ)]
    have hsum : α₀ * (1 - θ) + α₁ * θ = 1 := by
      rw [mul_comm α₀ (1 - θ), mul_comm α₁ θ]; exact hα
    rw [hsum, Real.rpow_one]
  -- the same for `y`
  have hyy : y ^ (β₀ * (1 - θ)) * y ^ (β₁ * θ) = y := by
    rw [← Real.rpow_add hy (β₀ * (1 - θ)) (β₁ * θ)]
    have hsum : β₀ * (1 - θ) + β₁ * θ = 1 := by
      rw [mul_comm β₀ (1 - θ), mul_comm β₁ θ]; exact hβ
    rw [hsum, Real.rpow_one]
  -- commute the six factors so that the `x`-powers are adjacent (and likewise the `y`-powers)
  have rearr : m₀ ^ (1 - θ) * x ^ (α₀ * (1 - θ)) * y ^ (β₀ * (1 - θ)) *
        (m₁ ^ θ * x ^ (α₁ * θ) * y ^ (β₁ * θ))
      = m₀ ^ (1 - θ) * m₁ ^ θ * (x ^ (α₀ * (1 - θ)) * x ^ (α₁ * θ)) *
        (y ^ (β₀ * (1 - θ)) * y ^ (β₁ * θ)) := by ring
  rw [key m₀ α₀ β₀ (1 - θ) hm₀, key m₁ α₁ β₁ θ hm₁, rearr, hxx, hyy]

end Work.Analysis.Interpolation
