/-
# ZeroFreeTables — `tf71Q_defs`

An explicit antiderivative for `t ↦ e^{λt} · tf71cf θ lam t` on `[0, 2γ]`,
used to evaluate the Laplace transform `tf71Fc θ lam (-λ)` in closed form.

Writing `T = tan θ`, `A = λ (1 + T²) = λ + λT²`, `ζ = λT`, `γ = θ/ζ` and the
double-angle constant `β = 2 cot θ - cot 2θ`, the closed form `tf71cf` of the
test function on `[0,2γ]` reads

  `tf71cf θ lam t = A · ( (Aγ - 1 - (A/2) t) cos(ζt) + β sin(ζt) + (2λγ - 2 - λt) )`,

so an antiderivative for `e^{λt} tf71cf θ lam t` is
`e^{λt} · A · ( (u₀ + u₁ t) cos(ζt) + (v₀ + v₁ t) sin(ζt) + (w₀ + w₁ t) )` with

* `u₁ = -1/2`, `u₀ = γ - 1/(2λ) - β T/A`,
* `v₁ = -T/2`,  `v₀ = θ/λ + β/A`,
* `w₁ = -1`,   `w₀ = 2γ - 1/λ`.

This is exactly `tf71Q` below.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

/-- `A = λ(1 + tan²θ)`: the prefactor of `tf71cf`. -/
def tf71A (θ lam : ℝ) : ℝ := lam * (1 + Real.tan θ ^ 2)

/-- The double-angle constant `β = 2 cot θ - cot 2θ = 2 (tan θ)⁻¹ - (tan 2θ)⁻¹`. -/
def tf71β (θ : ℝ) : ℝ := 2 * (Real.tan θ)⁻¹ - (Real.tan (2 * θ))⁻¹

/-- Constant term of the `cos`-coefficient of the antiderivative `tf71Q`. -/
def tf71Qu (θ lam : ℝ) : ℝ :=
  tf71γ θ lam - 1 / (2 * lam) - tf71β θ * Real.tan θ / tf71A θ lam

/-- Constant term of the `sin`-coefficient of the antiderivative `tf71Q`. -/
def tf71Qv (θ lam : ℝ) : ℝ := θ / lam + tf71β θ / tf71A θ lam

/-- Explicit antiderivative of `t ↦ e^{λt} * tf71cf θ lam t`. -/
def tf71Q (θ lam : ℝ) (t : ℝ) : ℝ :=
  tf71A θ lam * Real.exp (lam * t) *
    ( (tf71Qu θ lam - (1 / 2) * t) * Real.cos (tf71ζ θ lam * t)
      + (tf71Qv θ lam - (Real.tan θ / 2) * t) * Real.sin (tf71ζ θ lam * t)
      + (2 * tf71γ θ lam - 1 / lam - t) )

end Work.ZeroFreeTables
