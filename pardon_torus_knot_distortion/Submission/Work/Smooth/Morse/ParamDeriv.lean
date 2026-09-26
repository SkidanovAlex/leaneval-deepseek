import Mathlib
import Submission.Work.Smooth.Morse.Defs

/-!
# The derivative of the torus parametrisation

The parametrisation of the standard torus of revolution,

`torusMap θ φ = ((2 + cos φ) cos θ, (2 + cos φ) sin θ, sin φ)`,

has the two partial derivatives

`dtheta = (-(2 + cos φ) sin θ, (2 + cos φ) cos θ, 0)`,
`dphi   = (- sin φ cos θ, - sin φ sin θ, cos φ)`,

which are linearly independent everywhere — their cross product is `(2 + cos φ) · (unit vector)`
whose norm is `2 + cos φ ≥ 1`.  Consequently `torusMap` is an immersion, and so is its composition
with any diffeomorphism of `ℝ³`.

This file defines the derivative `torusDeriv` and its two columns `dtheta`, `dphi`, together with
their component lemmas.  The two substantial facts are the Fréchet derivative of `torusMap`
(`Submission.Work.Smooth.Morse.Immersion.hasFDerivAt_torusMap`) and the linear independence of its
columns (`Submission.Work.Smooth.Morse.Immersion.torusDeriv_injective`); they are proved in
sub-files of `Submission/Work/Smooth/Morse/Immersion/`, and assembled into `isImmersion` in
`Submission.Work.Smooth.Morse.Immersion`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

/-- The `θ`-partial derivative of the torus parametrisation at `(θ,φ)`. -/
def dtheta (p : ℝ × ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then -(2 + Real.cos p.2) * Real.sin p.1
    else if i.val = 1 then (2 + Real.cos p.2) * Real.cos p.1
    else 0)

/-- The `φ`-partial derivative of the torus parametrisation at `(θ,φ)`. -/
def dphi (p : ℝ × ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then -Real.sin p.2 * Real.cos p.1
    else if i.val = 1 then -Real.sin p.2 * Real.sin p.1
    else Real.cos p.2)

@[simp] theorem dtheta_zero (p : ℝ × ℝ) :
    dtheta p 0 = -(2 + Real.cos p.2) * Real.sin p.1 := by
  simp only [dtheta, WithLp.ofLp_toLp]
  simp

@[simp] theorem dtheta_one (p : ℝ × ℝ) :
    dtheta p 1 = (2 + Real.cos p.2) * Real.cos p.1 := by
  simp only [dtheta, WithLp.ofLp_toLp]
  simp

@[simp] theorem dtheta_two (p : ℝ × ℝ) : dtheta p 2 = 0 := by
  simp only [dtheta, WithLp.ofLp_toLp]
  simp

@[simp] theorem dphi_zero (p : ℝ × ℝ) :
    dphi p 0 = -Real.sin p.2 * Real.cos p.1 := by
  simp only [dphi, WithLp.ofLp_toLp]
  simp

@[simp] theorem dphi_one (p : ℝ × ℝ) :
    dphi p 1 = -Real.sin p.2 * Real.sin p.1 := by
  simp only [dphi, WithLp.ofLp_toLp]
  simp

@[simp] theorem dphi_two (p : ℝ × ℝ) : dphi p 2 = Real.cos p.2 := by
  simp only [dphi, WithLp.ofLp_toLp]
  simp

/-- The Fréchet derivative of the torus parametrisation `(θ,φ) ↦ torusMap θ φ` at `(θ,φ)`,
written as the linear combination of the two columns `dtheta` and `dphi`. -/
def torusDeriv (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] R3 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (dtheta p) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (dphi p)

theorem torusDeriv_apply (p a : ℝ × ℝ) :
    torusDeriv p a = a.1 • dtheta p + a.2 • dphi p := by
  simp [torusDeriv, ContinuousLinearMap.smulRight_apply]

/-- The derivative of `torusMap` in the direction `(1,0)`. -/
theorem torusDeriv_fst (p : ℝ × ℝ) : torusDeriv p (1, 0) = dtheta p := by
  rw [torusDeriv_apply]; simp

/-- The derivative of `torusMap` in the direction `(0,1)`. -/
theorem torusDeriv_snd (p : ℝ × ℝ) : torusDeriv p (0, 1) = dphi p := by
  rw [torusDeriv_apply]; simp

/-- The `θ`-direction of the derivative of the parametrisation of the surface `F = ψ(S¹×S¹)`. -/
def paramDtheta (ψ : Submission.Diffeo) (p : ℝ × ℝ) : R3 :=
  fderiv ℝ (ψ : R3 → R3) (Work.Core.torusMap p.1 p.2) (dtheta p)

/-- The `φ`-direction of the derivative of the parametrisation of the surface `F = ψ(S¹×S¹)`. -/
def paramDphi (ψ : Submission.Diffeo) (p : ℝ × ℝ) : R3 :=
  fderiv ℝ (ψ : R3 → R3) (Work.Core.torusMap p.1 p.2) (dphi p)

/-- **`F = ψ(standard torus)` is a smoothly immersed surface**: the derivative of the
parametrisation `p ↦ ψ (torusMap p.1 p.2)` is injective at every parameter point. -/
def IsImmersion (ψ : Submission.Diffeo) : Prop :=
  ∀ p : ℝ × ℝ, Function.Injective (fderiv ℝ (param ψ) p)

end

end Work.Smooth.Morse
