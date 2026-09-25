import Mathlib
import Submission.Work.Core.Std

/-!
# The `(0,2)`-form `∂̄_J²u` and the integrability identity

This module introduces the explicit expression for the `(0,2)`-part of `d(∂̄_J u)` — the
"`∂̄²u`" of the classical `∂̄`-calculus — in the abstract picture of `Submission/Work/Core`
(`E n = ℝ^{2n}`, `Work.NN.Core`'s `Submission.dbar`).  The identity `∂̄_J²u = 0` for all smooth `u`
is the *integrability* of `J`: it holds exactly when the Nijenhuis tensor of `J` vanishes.

Recall from `Submission/Work/Core/Defs.lean` that `dbar J u x : E n →L[ℝ] ℂ` is the `(0,1)`-part
of `du` at `x`, so that `ω := dbar J u` is a `ℂ`-valued `1`-form.  Its exterior derivative at `x`,
on vectors `a, b`, is

  `delOne ω x a b = D_a (ω · b)(x) - D_b (ω · a)(x)`

(the standard formula for a `1`-form, using that the exterior derivative is the alternating part of
the first derivative), and the `(0,2)`-part of the `2`-form `dω` is

  `dbarSq J u x v w = (1/4)·(dω(v,w) + i·dω(Jv,w) + i·dω(v,Jw) - dω(Jv,Jw))`.

The classical computation gives `dbarSq J u x v w = du_x([v^{0,1}, w^{0,1}]^{1,0}(x))`, where
`v^{0,1}` denotes the `(0,1)`-projection of the constant vector field `v`; it therefore vanishes
identically as soon as `[T^{0,1}, T^{0,1}] ⊆ T^{0,1}`, i.e. as soon as the Nijenhuis tensor
vanishes.  Conversely, testing on the coordinate functions shows `dbarSq = 0` forces `N = 0`.
-/

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

namespace Work.NN.Core

variable {n : ℕ}

/-- The exterior derivative, at `x`, of the `ℂ`-valued `1`-form `z ↦ ω z`, evaluated on
`(a,b)`: `D_a(ω · b)(x) - D_b(ω · a)(x)`. -/
noncomputable def delOne (om : E n → E n →L[ℝ] ℂ) (x a b : E n) : ℂ :=
  fderiv ℝ (fun z => om z b) x a - fderiv ℝ (fun z => om z a) x b

/-- The `(0,2)`-part of `d(∂̄_J u)` at `x`, evaluated on `(v,w)`: the explicit `∂̄²u` of the
classical calculus. -/
noncomputable def dbarSq (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x v w : E n) : ℂ :=
  (1 / 4 : ℂ) *
    (delOne (dbar J u) x v w
      + Complex.I * delOne (dbar J u) x (J x v) w
      + Complex.I * delOne (dbar J u) x v (J x w)
      - delOne (dbar J u) x (J x v) (J x w))

end Work.NN.Core
