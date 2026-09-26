import Mathlib
import Submission.Work.Smooth.Morse.ParamDeriv

/-!
# `torusMap` is differentiable, with derivative `torusDeriv`

The parametrisation `torusMap θ φ = ((2 + cos φ) cos θ, (2 + cos φ) sin θ, sin φ)` of the
standard torus of revolution is the map `(θ, φ) ↦ WithLp.toLp 2 (componentwise formula)`.
To differentiate it we use the characterisation of `HasFDerivWithinAt` for `PiLp`-valued maps
(`hasFDerivWithinAt_piLp`): it suffices to differentiate the three coordinate functions

* `(θ, φ) ↦ (2 + cos φ) cos θ`,
* `(θ, φ) ↦ (2 + cos φ) sin θ`,
* `(θ, φ) ↦ sin φ`,

with respect to the coordinate functionals `PiLp.proj 2 _ i ∘SL torusDeriv p` of the candidate
derivative `torusDeriv p`.  Each of these is a scalar-valued function of `θ = q.1` and `φ = q.2`,
so it is differentiated by the product rule from `HasFDerivAt.cos`, `HasFDerivAt.sin` and
`HasFDerivAt.const_add`, together with the chain rule.

The three lemmas `proj_torusDeriv_zero/one/two` below identify those derivative functionals with
the (explicitly written) componentwise derivatives; they are the bookkeeping that connects the
abstract `torusDeriv` with the calculus.
-/

namespace Work.Smooth.Morse.Immersion

open LeanEval.KnotTheory.PardonDistortion

/-- The `θ`-coordinate functional of `torusDeriv p` is the derivative of the first coordinate
function `(θ, φ) ↦ (2 + cos φ) cos θ` of `torusMap`. -/
theorem proj_torusDeriv_zero (p : ℝ × ℝ) :
    (2 + Real.cos p.2) • ((-Real.sin p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ))
      + Real.cos p.1 • ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ))
      = (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0) ∘SL Work.Smooth.Morse.torusDeriv p := by
  refine ContinuousLinearMap.ext (fun a => ?_)
  have hfst : (ContinuousLinearMap.fst ℝ ℝ ℝ) a = a.1 := rfl
  have hsnd : (ContinuousLinearMap.snd ℝ ℝ ℝ) a = a.2 := rfl
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    Work.Smooth.Morse.torusDeriv_apply, PiLp.add_apply, PiLp.smul_apply, hfst, hsnd]
  simp only [Work.Smooth.Morse.dtheta, Work.Smooth.Morse.dphi, WithLp.ofLp_toLp]
  norm_num
  ring

/-- The `φ`-coordinate functional of `torusDeriv p` is the derivative of the second coordinate
function `(θ, φ) ↦ (2 + cos φ) sin θ` of `torusMap`. -/
theorem proj_torusDeriv_one (p : ℝ × ℝ) :
    (2 + Real.cos p.2) • (Real.cos p.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ))
      + Real.sin p.1 • ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ))
      = (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1) ∘SL Work.Smooth.Morse.torusDeriv p := by
  refine ContinuousLinearMap.ext (fun a => ?_)
  have hfst : (ContinuousLinearMap.fst ℝ ℝ ℝ) a = a.1 := rfl
  have hsnd : (ContinuousLinearMap.snd ℝ ℝ ℝ) a = a.2 := rfl
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    Work.Smooth.Morse.torusDeriv_apply, PiLp.add_apply, PiLp.smul_apply, hfst, hsnd]
  simp only [Work.Smooth.Morse.dtheta, Work.Smooth.Morse.dphi, WithLp.ofLp_toLp]
  norm_num
  ring

/-- The third coordinate functional of `torusDeriv p` is the derivative of the third coordinate
function `(θ, φ) ↦ sin φ` of `torusMap`. -/
theorem proj_torusDeriv_two (p : ℝ × ℝ) :
    Real.cos p.2 • (ContinuousLinearMap.snd ℝ ℝ ℝ)
      = (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2) ∘SL Work.Smooth.Morse.torusDeriv p := by
  refine ContinuousLinearMap.ext (fun a => ?_)
  have hsnd : (ContinuousLinearMap.snd ℝ ℝ ℝ) a = a.2 := rfl
  simp only [smul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    Work.Smooth.Morse.torusDeriv_apply, PiLp.add_apply, PiLp.smul_apply, hsnd]
  simp only [Work.Smooth.Morse.dtheta, Work.Smooth.Morse.dphi, WithLp.ofLp_toLp]
  norm_num
  ring

/-- **The torus parametrisation is differentiable, with derivative `torusDeriv`.** -/
theorem hasFDerivAt_torusMap (p : ℝ × ℝ) : HasFDerivAt (fun q : ℝ × ℝ => Work.Core.torusMap q.1 q.2) (Work.Smooth.Morse.torusDeriv p) p := by
  rw [← hasFDerivWithinAt_univ]
  rw [hasFDerivWithinAt_piLp]
  intro i
  rw [hasFDerivWithinAt_univ]
  -- the `φ`-part of the two product functions, shared by the first two coordinates
  have hcos2 : HasFDerivAt (fun x : ℝ × ℝ => Real.cos x.2)
      ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)).cos
  have hconst : HasFDerivAt (fun x : ℝ × ℝ => 2 + Real.cos x.2)
      ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := hcos2.const_add 2
  fin_cases i
  · -- first coordinate: `(θ, φ) ↦ (2 + cos φ) cos θ`
    simp only [Work.Core.torusMap, WithLp.ofLp_toLp]
    have hcos1 : HasFDerivAt (fun x : ℝ × ℝ => Real.cos x.1)
        ((-Real.sin p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ)).cos
    exact proj_torusDeriv_zero p ▸ (hconst.mul hcos1)
  · -- second coordinate: `(θ, φ) ↦ (2 + cos φ) sin θ`
    simp only [Work.Core.torusMap, WithLp.ofLp_toLp]
    have hsin1 : HasFDerivAt (fun x : ℝ × ℝ => Real.sin x.1)
        (Real.cos p.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ)).sin
    exact proj_torusDeriv_one p ▸ (hconst.mul hsin1)
  · -- third coordinate: `(θ, φ) ↦ sin φ`
    simp only [Work.Core.torusMap, WithLp.ofLp_toLp]
    have hsin2 : HasFDerivAt (fun x : ℝ × ℝ => Real.sin x.2)
        (Real.cos p.2 • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)).sin
    exact proj_torusDeriv_two p ▸ hsin2

end Work.Smooth.Morse.Immersion
