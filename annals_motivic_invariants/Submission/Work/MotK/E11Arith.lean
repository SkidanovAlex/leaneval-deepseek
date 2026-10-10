-- This file is a *copy* of `Submission/Work/MotK/Arith.lean` (whose declarations are renamed with
-- the prefix `e11_` so that the copy can be imported by `Submission/Work/MotK/ExistsKleinData.lean`
-- without an import cycle).  The proofs are unchanged.
import Mathlib
import Submission.Work.MotK.E11Model

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.e11_Arith`

The Tate normal form `E₁₁ : y² - 10xy - 11y = x³ - 11x²` (`b = 11`) is an elliptic curve
whose `j`-invariant is neither `0` nor `1728`, in every field in which `2`, `11` and `31`
are nonzero (equivalently: the standard hypotheses under which the Klein model of
`Submission/Work/MotK/ExistsKleinData.lean` is non-degenerate).

In any commutative ring the Weierstrass invariants of `E₁₁` are the integers

* `Δ = 11^5 (11^2 - 11·11 - 1) = -11^5 = -161051`,
* `c₄ = b₂² - 24 b₄ = 496 = 2^4 · 31`,
* `j = Δ⁻¹ c₄³ = -122023936 / 161051 = -2^12 · 31^3 / 11^5`,

so `E₁₁` is elliptic as soon as `11 ≠ 0`, and

* `j ≠ 0` because `31 ≠ 0` (and `2 ≠ 0`),
* `j ≠ 1728` because `122023936 + 1728·161051 = 400320064 ≠ 0`.

All three conditions are exactly the hypotheses `h11`, `h2`/`h31` and `h1728` of the
statement; nothing else (in particular no hypothesis on `3` or `5`) is used.
-/

set_option linter.style.haveILetI false

namespace Work.MotK

theorem e11_Arith (𝕜 : Type) [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0) (h31 : (31 : 𝕜) ≠ 0)
    (h11 : (11 : 𝕜) ≠ 0) (h1728 : (400320064 : 𝕜) ≠ 0) :
    ∃ (_ : (Work.MotK.E11 𝕜).IsElliptic),
      (Work.MotK.E11 𝕜).j ≠ 0 ∧ (Work.MotK.E11 𝕜).j ≠ 1728 := by
  -- `Δ(E₁₁) = -161051` and `c₄(E₁₁) = 496`, in any commutative ring.
  have hΔ : (Work.MotK.E11 𝕜).Δ = -(161051 : 𝕜) := by
    simp only [Work.MotK.E11, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    norm_num
  have hc4 : (Work.MotK.E11 𝕜).c₄ = (496 : 𝕜) := by
    simp only [Work.MotK.E11, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    norm_num
  -- the two numeral non-vanishing facts we need
  have h161051 : (161051 : 𝕜) ≠ 0 := by
    have h : (161051 : 𝕜) = (11 : 𝕜) ^ 5 := by norm_num
    rw [h]; exact pow_ne_zero 5 h11
  have h496 : (496 : 𝕜) ≠ 0 := by
    have h : (496 : 𝕜) = (2 : 𝕜) ^ 4 * 31 := by norm_num
    rw [h]; exact mul_ne_zero (pow_ne_zero 4 h2) h31
  -- `E₁₁` is elliptic since `Δ = -11^5 ≠ 0`.
  have hΔne : (Work.MotK.E11 𝕜).Δ ≠ 0 := by rw [hΔ]; exact neg_ne_zero.mpr h161051
  have hEll : (Work.MotK.E11 𝕜).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔne⟩
  letI := hEll
  -- `j = Δ⁻¹ c₄³ = 496³ / (-161051)`.
  have hj0 : (Work.MotK.E11 𝕜).j ≠ 0 := by
    rw [WeierstrassCurve.j_eq, hΔ, hc4]
    exact mul_ne_zero (inv_ne_zero (neg_ne_zero.mpr h161051)) (pow_ne_zero 3 h496)
  have hj1728 : (Work.MotK.E11 𝕜).j ≠ 1728 := by
    rw [WeierstrassCurve.j_eq, hΔ, hc4]
    intro h
    -- multiply `j = 1728` by `Δ = -161051` (nonzero) to clear the inverse
    have hmul : (-(161051 : 𝕜)) * ((-(161051 : 𝕜))⁻¹ * (496 : 𝕜) ^ 3)
        = (-(161051 : 𝕜)) * (1728 : 𝕜) := by
      rw [h]
    rw [← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.mpr h161051), one_mul] at hmul
    -- `496³ = 1728 · (-161051)`, i.e. `400320064 = 0`, contradicting `h1728`.
    have key : (496 : 𝕜) ^ 3 - (1728 : 𝕜) * (-(161051 : 𝕜)) = 0 := by rw [hmul]; ring
    norm_num at key
    exact h1728 key
  exact ⟨hEll, hj0, hj1728⟩

end Work.MotK
