import Mathlib
import Submission.Work.RPB.Defs

/-!
# Vocabulary for `Work.RPB.B1.area_pos_of_isotopy`

The signed area `∮ ω_ℂ (c, c')` of a closed plane curve is `± 2 ×` the area of the region it
bounds, hence never vanishes on an embedded curve.  The route formalised here is the classical
"flux" computation of the (analytic) winding number:

* `windInt u q` is the winding number of the closed curve `u` about `q`,
  `(1/2π) ∮ Im (u'/(u-q))`;
* `windInt u ·` is integer valued and locally constant off `u` (it is the degree of the direction
  map), vanishes outside the disc containing `u`, and is non-zero somewhere for an embedded `u`;
* the flux identity `∫_ℂ windInt u = (1/2) ∮ ω_ℂ (u, u')` then identifies the signed area with
  `2 ×` (area of the bounded component), via `fluxR` and its limit.

This file contains only the vocabulary (the definitions); the lemmas live in the sibling modules
`Submission.Work.RPB.B1.*` and in `Submission.Work.RPB.B1.area_pos_of_isotopy`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1

/-- **The winding number of a closed curve about a point**, in integral form:
`windInt u q = (1/2π) ∮_0^{2π} Im (u'(t) / (u t - q)) dt`.

The value at `q ∈ range u` is junk (the integrand has a singularity there); every statement about
`windInt` below either assumes `q ∉ range u` or integrates over a set of full measure. -/
def windInt (u : ℝ → ℂ) (q : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t - q)).im

/-- The explicit radial-coordinate expression for the flux of the winding integrand through the
disc `B(0,R)`: for `‖u t‖ < R` and `q = r e^{iθ}`, the radial range of `q` in the disc centred at
`u t` is `[0, r₊(t,θ)]` with `r₊ = Re (u t · e^{-iθ}) + √(R² - Im (u t · e^{-iθ})²)`, so

`fluxR u R = (1/2π) ∫_0^{2π} ∫_0^{2π} Im (u'(t) e^{-iθ}) ·
   (Re (u t e^{-iθ}) + √(R² - Im (u t e^{-iθ})²)) dθ dt`.

The identity `∫_{B_R} windInt u = fluxR u R` is `Submission.Work.RPB.B1.windInt_ball_integral`,
and `fluxR u R → (1/2) ∮ ω_ℂ (u, u')` as `R → ∞` is `Submission.Work.RPB.B1.fluxR_tendsto`. -/
def fluxR (u : ℝ → ℂ) (R : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi),
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im *
        ((u t * Complex.exp (-(θ : ℂ) * Complex.I)).re +
          Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2))

end Work.RPB.B1
