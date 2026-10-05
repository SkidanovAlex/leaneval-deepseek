import Mathlib

/-!
# Definitions for the polar computation of `Work.RPB.B1.polarKernel`

The aim of the surrounding development is the identity

`∫ q in ball 0 R, (C / (a - q)).im
   = ∫ θ in 0..2π, (C e^{-iθ}).im * (Re (a e^{-iθ}) + sqrt (R² - Im (a e^{-iθ})²))`

for `‖a‖ < R`.  The right hand side is exactly the polar parametrisation of the disc `ball 0 R`
centred at the pole `a`: writing `u = a - q = ρ e^{iφ}` the radial extent of the (translated)
ball `ball a R` in the direction `φ` is `Re (a e^{-iφ}) + sqrt (R² - Im (a e^{-iφ})²)`, which is
the function `radial` defined below.

This file only collects the definitions (and the continuity of `Complex.polarCoord.symm`), so that
the individual algebraic / measure-theoretic lemmas can be stated in this vocabulary.
-/

namespace Work.RPB.B1

open MeasureTheory Set Complex Real
open scoped Real

noncomputable section

/-- The radial extent of the disc `ball a R` in the polar direction encoded by `e^{-i φ}`:
`Re (a e^{-iφ}) + sqrt (R² - Im (a e^{-iφ})²)`. -/
def radial (a : ℂ) (R φ : ℝ) : ℝ :=
  (a * Complex.exp (-(φ : ℂ) * Complex.I)).re +
    Real.sqrt (R ^ 2 - (a * Complex.exp (-(φ : ℂ) * Complex.I)).im ^ 2)

/-- The (total) inverse of the polar coordinate homeomorphism, `(r, φ) ↦ r e^{i φ}`, is continuous
as a map `ℝ × ℝ → ℂ`. -/
theorem continuous_polarCoord_symm :
    Continuous (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ)) := by
  have h : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ))
      = fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
    funext p
    rw [Complex.polarCoord_symm_apply]
  rw [h]
  fun_prop

/-- The target of the polar coordinate homeomorphism `Complex.polarCoord`. -/
def polarTarget : Set (ℝ × ℝ) := Complex.polarCoord.target

theorem measurableSet_polarTarget : MeasurableSet polarTarget :=
  Complex.polarCoord.open_target.measurableSet

/-- The polar-coordinate description of the ball `ball a R`: `p` is sent into the ball by
`(r, φ) ↦ r e^{iφ}`. -/
def ballRegion (a : ℂ) (R : ℝ) : Set (ℝ × ℝ) :=
  {p | (Complex.polarCoord.symm p : ℂ) ∈ Metric.ball a R}

theorem measurableSet_ballRegion (a : ℂ) (R : ℝ) : MeasurableSet (ballRegion a R) := by
  have h : ballRegion a R
      = (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ) - a) ⁻¹' Metric.ball (0 : ℂ) R := by
    ext p; simp [ballRegion, Metric.mem_ball, dist_eq_norm]
  rw [h]
  exact (Metric.isOpen_ball.preimage
    (continuous_polarCoord_symm.sub continuous_const)).measurableSet

/-- The angular kernel `p ↦ (C e^{-i p.2}).im` appearing on the right hand side. -/
def kernel (C : ℂ) (p : ℝ × ℝ) : ℝ :=
  (C * Complex.exp (-(p.2 : ℂ) * Complex.I)).im

/-- The polar-coordinate integrand obtained after the polar change of variables: the (radial)
indicator of the disc `ball a R` times the angular kernel.  On the polar target this is
`1_{ρ < radial a R φ} · (C e^{-iφ}).im`. -/
def polarIntegrand (a C : ℂ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < radial a R p.2 then (C * Complex.exp (-(p.2 : ℂ) * Complex.I)).im else 0

end

end Work.RPB.B1
