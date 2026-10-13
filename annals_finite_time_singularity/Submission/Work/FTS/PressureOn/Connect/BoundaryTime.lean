/-
# `Work.FTS.PressureOn.Connect.BoundaryTime` — the one-sided (boundary-time) data

The target `Connect.contDiffWithinAt_potOn_at_zero` is the statement that the reconstructed
potential `q = potOn ω` is `C¹` on the closed half-strip `ℝ³ × [0,T)` *at the boundary time*
`t = 0`.  The data of the hypotheses are one sided: `∂ₜω` is only known on `[0,T)`, the
vorticity slices are right differentiable at `0`, and the velocity is jointly `C^{1,α}` on the
closed strips.  Consequently the *right* time derivative of a slice at `t = 0` is what enters,
whereas Lean's two sided `deriv` (i.e. `FiniteTimeSingularity.timeDeriv`) is the junk value `0`
whenever the left and the right derivatives differ — which is the generic situation here, since
the values of `ω` at negative times are completely unconstrained by the hypotheses.

This file collects the objects that make the one sided analysis work:

* `bstrip T` — the closed strip `ℝ³ × [0, T/2]` on which the boundary analysis is performed;
* `tblock ω T x` — the *right* time derivative of the velocity slice `s ↦ u x s` at `s = 0`,
  read off from the time block of the within derivative `fderivWithin ℝ u.uncurry (bstrip T)`;
* `dtLamb ω T y` — the right time derivative of the Lamb vector slice at `s = 0`, namely
  `(∂ₜu)(y,0) × ω(y,0) + u(y,0) × (∂ₜω)(y,0)` (product rule);
* `lambExt ω T` — the time retraction of the Lamb vector which agrees with it on `[0, T/2]` and
  extends it to negative times by the *affine* continuation with slope `dtLamb`, so that the
  two sided `timeDeriv` of `lambExt` at `0` is the right derivative `dtLamb` and is continuous;
* `potTDerivExt ω T` — the (Newtonian) time derivative of the potential of `lambExt`, which is
  the continuous extension of `potTDeriv ω` to the closed strip;
* `potGradExt ω T` — the continuous extension of the space gradient `∂ₜu - u×ω` to the
  boundary time; and `potFDerivExt ω T` the resulting full derivative field of `q.uncurry`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.Connect.Deriv
import Submission.Work.FTS.PressureOn.Connect.Clamp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

/-- The closed strip `ℝ³ × [0, T/2]` on which the boundary-time analysis is carried out. -/
def bstrip (T : ℝ) : Set (R3 × ℝ) := Set.univ ×ˢ Set.Icc 0 (T / 2)

/-- **The right time derivative of the velocity at the boundary time.**
It is the time block of the within derivative of the uncurried velocity on the strip. -/
def tblock (ω : R3 → ℝ → R3) (T : ℝ) (x : R3) : R3 :=
  fderivWithin ℝ (physVel ω).uncurry (bstrip T) (x, 0) ((0 : R3), 1)

/-- **The right time derivative of the Lamb vector at the boundary time**, obtained from the
product rule: `∂ₜ(u × ω) = (∂ₜu) × ω + u × (∂ₜω)`, all derivatives being the right ones. -/
def dtLamb (ω : R3 → ℝ → R3) (T : ℝ) (y : R3) : R3 :=
  crossVec (tblock ω T y) (ω y 0) + crossVec (physVel ω y 0) (timeDeriv ω y 0)

/-- **The time retraction of the Lamb vector**: it agrees with `lamb` on `[0, T/2]` and extends
it affinely to negative times with slope the right derivative `dtLamb`, so that its two sided
`timeDeriv` at `0` is `dtLamb`. -/
def lambExt (ω : R3 → ℝ → R3) (T : ℝ) : R3 → ℝ → R3 :=
  fun y t => if t ≤ 0 then lamb (physVel ω) ω y 0 + t • dtLamb ω T y
    else lamb (physVel ω) ω y t

/-- **The time derivative of the potential, extended to the boundary time**: the Newtonian time
derivative of the retracted Lamb field `lambExt`.  On `[0, T/2]` this is `potTDeriv ω`, and at
`t = 0` it is the limit of the one sided derivatives. -/
def potTDerivExt (ω : R3 → ℝ → R3) (T : ℝ) : R3 → ℝ → ℝ :=
  fun x t => -∫ y, inner ℝ (nablaNfund (x - y)) (timeDeriv (lambExt ω T) y t)

/-- **The space gradient of the potential, extended to the boundary time**: `∂ₜu - u × ω` for
`t > 0`, and its limit `tblock - u × ω` at `t = 0`. -/
def potGradExt (ω : R3 → ℝ → R3) (T : ℝ) : R3 × ℝ → R3 :=
  fun p => if p.2 = 0 then tblock ω T p.1 - crossVec (physVel ω p.1 0) (ω p.1 0)
    else timeDeriv (physVel ω) p.1 p.2 - crossVec (physVel ω p.1 p.2) (ω p.1 p.2)

/-- **The full extended derivative field** of the uncurried potential on the closed strip. -/
def potFDerivExt (ω : R3 → ℝ → R3) (T : ℝ) : R3 × ℝ → (R3 × ℝ →L[ℝ] ℝ) :=
  fun p => (innerSL ℝ (potGradExt ω T p)).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
    + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) (potTDerivExt ω T p.1 p.2)

end

end Work.FTS.PressureOn.Connect
