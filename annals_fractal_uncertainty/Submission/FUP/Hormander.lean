import Submission.FUP.Dbar

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# Hörmander's `L²` theorem for the `∂̄`-operator

Hörmander's theorem (Thm 2.2.1' of *An Introduction to Complex Analysis in Several Variables*),
in the form stated as Theorem `thm:hormander_delbar` of Cohen's §5: if `φ` is plurisubharmonic
with `∂∂̄φ ≥ κ > 0` in the distributional sense and `η` is a `∂̄`-closed `(0,1)`-form with
`∫|η|²e^{-φ}/κ < ∞`, then `∂̄g = η` has a smooth solution with `∫|g|²e^{-φ} ≤ ∫|η|²e^{-φ}/κ`.

This is a *specification*: it is a classical textbook theorem, but its proof (the Bochner–Kodaira
identity plus the twisted `L²` estimate and the density of smooth forms) is far outside the
present development, exactly as Han–Schlag's Theorem 5.1 is.  Everything else in §5 is proved.
-/

namespace Submission.FUP

/-- **Hörmander's `∂̄` theorem** (Cohen's `thm:hormander_delbar`).

Note the two smoothness hypotheses: the data `η` is required to be `C^∞`, and the solution `g` is
then `C^∞` (this is Hörmander's theorem together with the elliptic regularity of `∂̄`, which is
what makes the equation `∂̄g = η` hold *pointwise*, as §5 needs).  Without the smoothness of `η`
the statement would be false: `DbarClosed` is a condition involving `fderiv`, hence vacuous at
every point where `η` fails to be differentiable, so there are non-smooth `η` with a weighted
`L²` bound for which no smooth solution exists. -/
def HormanderStatement : Prop :=
  ∀ (φ : ℂᵈ → ℝ) (κ : ℂᵈ → ℝ), DbarDbarPos φ κ → (∀ z, 0 < κ z) →
    ∀ (η : ℂᵈ → (Fin d → ℂ)), DbarClosed η → ContDiff ℝ ∞ η →
      (∫⁻ z, ENNReal.ofReal (formNormSq η z * Real.exp (-(φ z)) / κ z) < ⊤) →
      ∃ g : ℂᵈ → ℂ, ContDiff ℝ ∞ g ∧
        (∀ j : Fin d, (fun z => partialZbar j g z) = fun z => η z j) ∧
        (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(φ z)))
          ≤ ∫⁻ z, ENNReal.ofReal (formNormSq η z * Real.exp (-(φ z)) / κ z))

end Submission.FUP
