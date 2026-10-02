/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Interface for the repelling coordinate at a parabolic germ

This file sets up the vocabulary used to construct the *repelling coordinate* of the parabolic
germ `f z = z + z ^ 2 * h z` (with `h 0 = 1`, `ParabolicBounds f h a r A A'`), i.e. a
holomorphic solution `V` of the conjugacy equation

`V (w + 1) = wMap f (V w)`

on a left half-plane `{w | Re w < -R}`, with `V w ≈ w`.  Writing `Ψ w = -1 / V w` this is
exactly the repelling coordinate `IsRepellingCoord f 0 R Ψ` in the chart `w = -1/z`.

The construction uses the *corrected* ansatz `V w = w + c * Λ w + Z w` with `c = 1 - a` and

* `Λ w = log (-w) + π i`, a single-valued branch of `w ↦ log w` on the whole left half-plane
  (so `Λ (w + 1) - Λ w = log (1 + 1/w)` there);
* `Z` a *bounded* correction, obtained as the fixed point of a contraction on the half-plane.

The *defect* of the ansatz is `defect f a w ζ`, and `Ω` is the operator whose fixed point is the
correction `Z`.
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.FatouCoord.Petal

noncomputable section

/-- The branch of the logarithm on the left half-plane `{Re w < 0}`: `Λ w = log (-w) + π i`.
It is holomorphic on `{Re w < 0}` and satisfies `Λ (w + 1) - Λ w = log (1 + 1/w)` there. -/
def Lambda (w : ℂ) : ℂ := Complex.log (-w) + (Real.pi : ℂ) * Complex.I

/-- The main correction term of the approximate repelling conjugacy: `(1 - a) * Λ w`. -/
def corr (a : ℂ) (w : ℂ) : ℂ := (1 - a) * Lambda w

/-- The defect of the approximate solution `V₀ w = w + corr a w` of the conjugacy equation
`V (w + 1) = wMap f (V w)`:
`defect f a w ζ = wMap f (w + corr a w + ζ) - (w + corr a w + ζ) - 1 - (1 - a) (Λ (w+1) - Λ w)`. -/
def defect (f : ℂ → ℂ) (a : ℂ) (w ζ : ℂ) : ℂ :=
  wMap f (w + corr a w + ζ) - (w + corr a w + ζ) - 1 - (1 - a) * (Lambda (w + 1) - Lambda w)

/-- The half-plane on which the construction is carried out. -/
def LeftHalfPlane (R : ℝ) : Set ℂ := {w : ℂ | w.re < -R}

@[simp] theorem mem_LeftHalfPlane {R : ℝ} {w : ℂ} : w ∈ LeftHalfPlane R ↔ w.re < -R := Iff.rfl

theorem IsOpen_leftHalfPlane (R : ℝ) : IsOpen (LeftHalfPlane R) :=
  isOpen_lt Complex.continuous_re continuous_const

theorem Lambda_apply (w : ℂ) : Lambda w = Complex.log (-w) + (Real.pi : ℂ) * Complex.I := rfl

theorem corr_apply (a w : ℂ) : corr a w = (1 - a) * Lambda w := rfl

theorem defect_apply (f : ℂ → ℂ) (a w ζ : ℂ) :
    defect f a w ζ
      = wMap f (w + corr a w + ζ) - (w + corr a w + ζ) - 1
        - (1 - a) * (Lambda (w + 1) - Lambda w) := rfl

/-- The fixed-point operator of the correction `Z`.  A function `Z : ℂ → ℂ` solves
`Z (w + 1) - Z w = defect f a w (Z w)` on the left half-plane `{Re w < -R}` iff it is a fixed
point of `Omega`: summing the difference equation along the leftward orbit gives

`Z w = ∑' n, defect f a (w - n - 1) (Z (w - n - 1))`.

Because `‖defect f a x ζ‖ ≤ K (1 + log ‖x‖) / ‖x‖²` (uniformly in `‖ζ‖ ≤ 1`), the operator
`Omega` is a contraction with ratio `≤ K'/R` on the space of bounded functions with
`‖Z w‖ ≤ 1/2`, and its fixed point is the required correction. -/
def Omega (f : ℂ → ℂ) (a : ℂ) (Z : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, defect f a (w - ((n : ℕ) + 1)) (Z (w - ((n : ℕ) + 1)))

theorem Omega_apply (f : ℂ → ℂ) (a : ℂ) (Z : ℂ → ℂ) (w : ℂ) :
    Omega f a Z w = ∑' n : ℕ, defect f a (w - ((n : ℕ) + 1)) (Z (w - ((n : ℕ) + 1))) := rfl

end

end Work.FatouCoord.Petal
