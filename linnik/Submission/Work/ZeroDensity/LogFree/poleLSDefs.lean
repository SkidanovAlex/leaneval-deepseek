import Mathlib
import Submission.Work.ZeroDensity.LogFree.RouteDefs

/-!
# `Work.ZeroDensity.LogFree.poleLSDefs` — shared vocabulary for the pole large sieve (L4)

This file fixes the exact interface of the mean value theorem for `1/L`-separated frequencies
that the damped pole bound (`poleLargeSieve`, L4 of `JUTILA_UNIFIED_LEAD.md` §3) consumes.
It is stated for a *constant* `C`, so that a prover of a downstream lemma can take it as an
explicit hypothesis without depending on the module that proves it.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

/-- **The multiplicative (log-variable) mean value bound for separated frequencies.**

For every `δ > 0`, all `δ`-separated real frequencies `γ` and all coefficients `ζ`, the mean
square of `∑ i, ζ i · y^{-i γ i}` over an interval `[Y₁, Y₂] ⊂ (0,∞)` with respect to the
multiplicative measure `dy / y` is at most `(log (Y₂/Y₁) + 100/δ) · ∑ ‖ζ i‖²`.

Equivalently (substituting `y = e^t`) this is the classical mean value theorem
`∫_a^b ‖∑ i, ζ i e^{-i γ i t}‖² dt ≤ ((b-a) + 100/δ) ∑ ‖ζ i‖²` for `δ`-separated `γ i`. -/
def MvtMul (C : ℝ) : Prop :=
  ∀ (δ : ℝ), 0 < δ → ∀ (m : ℕ) (γ : Fin m → ℝ) (ζ : Fin m → ℂ) (Y₁ Y₂ : ℝ),
    0 < Y₁ → Y₁ ≤ Y₂ → (∀ i j, i ≠ j → δ ≤ |γ i - γ j|) →
    (∫ y in Y₁..Y₂, ‖∑ i, ζ i * (y : ℂ) ^ (-(γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      ≤ (Real.log (Y₂ / Y₁) + C / δ) * ∑ i, ‖ζ i‖ ^ 2

end Work.ZeroDensity.LogFree
