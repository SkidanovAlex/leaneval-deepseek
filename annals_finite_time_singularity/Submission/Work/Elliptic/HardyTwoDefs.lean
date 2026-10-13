/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary quantities for `Work.Elliptic.hardy_two`

`hardy_two` is Lemma `HardyInequality2` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887,

namely, for `f : ℝ → ℝ` of class `C²` on `[0,π/2]` with `f 0 = f (π/2) = 0`,

  `∫_0^{π/2} (∂_θ (f/sin 2θ))² ≤ 10 ∫_0^{π/2} (f'')²`.

The proof implemented in `hardy_two` is an exact integration by parts: writing
`u = f / sin(2θ)` (so `f'' = sin(2θ) u'' + 4 cos(2θ) u' - 4 sin(2θ) u`), one has the
*pointwise* identity

  `10 (f'')² - (u')² - (10 sin²(2θ) u''² + (79 + 80 sin²(2θ)) u'² + 160 sin²(2θ) u²)
      = (40 sin(2θ) cos(2θ) u'² - 80 sin²(2θ) u u')'`,

the middle parenthesis being pointwise nonnegative.  Integrating over `[0,π/2]` and
using that the antiderivative vanishes at both endpoints gives the inequality with the
constant `10` (indeed with `10` on the nose from the nonnegativity, and in fact the
sharper `∫(u')² ≤ (1/8)∫(f'')²` is available from the same computation).

This file only fixes the notation; the analytic lemmas live in
`Work.Elliptic.hardy_two_analytic` and `Work.Elliptic.hardy_two_deriv`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The function `u θ = f θ / sin(2θ)` whose derivative is estimated by `hardy_two`.
At `θ = 0, π/2` it takes the (irrelevant) default value `0`. -/
def htU (f : ℝ → ℝ) : ℝ → ℝ := fun θ => f θ / Real.sin (2 * θ)

/-- The pointwise nonnegative quantity
`10 sin²(2θ) u''² + (79 + 80 sin²(2θ)) u'² + 160 sin²(2θ) u²`. -/
def htNN (f : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  10 * (Real.sin (2 * θ)) ^ 2 * (deriv (deriv (htU f)) θ) ^ 2
    + (79 + 80 * (Real.sin (2 * θ)) ^ 2) * (deriv (htU f) θ) ^ 2
    + 160 * (Real.sin (2 * θ)) ^ 2 * (htU f θ) ^ 2

/-- The antiderivative `40 sin(2θ) cos(2θ) u'² - 80 sin²(2θ) u u'` of the deficit of the
integration by parts in `hardy_two`. -/
def htPP (f : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  40 * Real.sin (2 * θ) * Real.cos (2 * θ) * (deriv (htU f) θ) ^ 2
    - 80 * (Real.sin (2 * θ)) ^ 2 * (htU f θ) * (deriv (htU f) θ)

/-- The pointwise deficit `10 f''² - u'² - htNN`; it equals `(htPP f)'` on `(0,π/2)`. -/
def htEE (f : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  10 * (deriv (deriv f) θ) ^ 2 - (deriv (htU f) θ) ^ 2 - htNN f θ

/-- `htNN` is pointwise nonnegative. -/
theorem htNN_nonneg (f : ℝ → ℝ) (θ : ℝ) : 0 ≤ htNN f θ := by
  have h1 : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ 79 + 80 * (Real.sin (2 * θ)) ^ 2 := by linarith [h1]
  have h3 : (0 : ℝ) ≤ 10 * (Real.sin (2 * θ)) ^ 2 * (deriv (deriv (htU f)) θ) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) h1) (sq_nonneg _)
  have h4 : (0 : ℝ) ≤ (79 + 80 * (Real.sin (2 * θ)) ^ 2) * (deriv (htU f) θ) ^ 2 :=
    mul_nonneg h2 (sq_nonneg _)
  have h5 : (0 : ℝ) ≤ 160 * (Real.sin (2 * θ)) ^ 2 * (htU f θ) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) h1) (sq_nonneg _)
  simp only [htNN]
  linarith

/-- `htEE f θ = 10 f''(θ)² - u'(θ)² - htNN f θ` unfolds to the pointwise identity
`u'(θ)² = 10 f''(θ)² - htNN f θ - htEE f θ`. -/
theorem ht_sq_eq (f : ℝ → ℝ) (θ : ℝ) :
    (deriv (htU f) θ) ^ 2 = 10 * (deriv (deriv f) θ) ^ 2 - htNN f θ - htEE f θ := by
  simp only [htEE]; ring

theorem htPP_zero (f : ℝ → ℝ) : htPP f 0 = 0 := by
  simp [htPP]

theorem htPP_pi2 (f : ℝ → ℝ) : htPP f (π / 2) = 0 := by
  have h : Real.sin (2 * (π / 2)) = 0 := by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
  simp [htPP, h]

end Work.Elliptic
