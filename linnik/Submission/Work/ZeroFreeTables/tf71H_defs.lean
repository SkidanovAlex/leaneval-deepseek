/-
# `tf71H` — an explicit antiderivative of the HB §7 test-function closed form

For `tf71cf θ lam` (the closed form of the test function `f = g ⊛ g` of
`testFn71_defs`), the function `tf71H θ lam` defined here is a global
antiderivative: `tf71H θ lam` has derivative `tf71cf θ lam` at every point.

It is obtained by integrating `tf71cf θ lam` term by term:

* `λ(1+tan²θ) · ∫ (γ − x/2) cos(ζx) dx = λ(1+tan²θ)² [(γ − x/2) sin(ζx)/ζ − cos(ζx)/(2ζ²)]`
* `λ(1+tan²θ) · ∫ λ(2γ − x) dx = λ(1+tan²θ) · λ(2γx − x²/2)`
* `λ(1+tan²θ) · ∫ sin(2θ − ζx)/sin(2θ) dx = λ(1+tan²θ) cos(2θ − ζx)/(ζ sin 2θ)`
* `λ(1+tan²θ) · ∫ (−2) dx = −2λ(1+tan²θ) x`
* `λ(1+tan²θ) · ∫ (−2 sin(θ − ζx)/sin θ) dx = −2λ(1+tan²θ) cos(θ − ζx)/(ζ sin θ)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

/-- An explicit global antiderivative of `tf71cf θ lam`. -/
def tf71H (θ lam : ℝ) (x : ℝ) : ℝ :=
  lam * (1 + Real.tan θ ^ 2) *
    ( lam * (1 + Real.tan θ ^ 2) *
        ((tf71γ θ lam - x / 2) * Real.sin (tf71ζ θ lam * x) / tf71ζ θ lam
          - Real.cos (tf71ζ θ lam * x) / (2 * tf71ζ θ lam ^ 2))
      + lam * (2 * tf71γ θ lam * x - x ^ 2 / 2)
      + Real.cos (2 * θ - tf71ζ θ lam * x) / (tf71ζ θ lam * Real.sin (2 * θ))
      - 2 * x
      - 2 * Real.cos (θ - tf71ζ θ lam * x) / (tf71ζ θ lam * Real.sin θ) )

end Work.ZeroFreeTables
