/-
Copyright: work module for the Elgindi finite-time singularity project.

# The one-dimensional angular calculus behind `DivisionBySin`

`DivisionBySin` compares the `H^4`-norm of `Φ / sin(2θ)` with that of `∂_θΦ`.  Because
`D_z = z∂_z` and the angular weights depend only on `θ`, every angular estimate needed
is a *one-dimensional* statement about a single `θ`-slice `h` of `Φ`.  This file fixes
the vocabulary of that one-dimensional calculus:

* `Dth1 h = sin(2θ) · h'` — the restriction of `D_θ` to functions of `θ` alone;
* `Dth1Iter n h` — its `n`-th iterate;
* `SinQ h = h / sin(2θ)` — the angular quotient;
* `SmoothSlice h` — `h` is smooth on an open neighbourhood of the closed interval
  `Iθ = [0, π/2]`, which is what the `θ`-slice of a `SmoothNbhd` function satisfies.

All the substantive content (weighted Hardy inequality, the base-case estimate for
`D_θ (h/sin 2θ)`, the higher-order recursion, endpoint bounds and integrability) lives
in the modules `DivSinHardy`, `DivSinBase`, `DivSinIter`, `SinSliceBounds`, `DivSinInt`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The angular operator `D_θ = sin(2θ) ∂_θ` acting on functions of `θ` alone. -/
def Dth1 (f : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv f θ

/-- The `n`-th iterate of `Dth1`. -/
def Dth1Iter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dth1 (Dth1Iter n f)

/-- The angular quotient `h ↦ h / sin(2θ)`. -/
def SinQ (h : ℝ → ℝ) : ℝ → ℝ := fun θ => h θ / Real.sin (2 * θ)

/-- `h` is smooth on an open neighbourhood of the closed interval `Iθ = [0, π/2]`;
this is exactly what the `θ`-slice of a `SmoothNbhd` function satisfies. -/
def SmoothSlice (h : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ h (Set.Ioo (-1) (Real.pi / 2 + 1))

@[simp] theorem Dth1Iter_zero (f : ℝ → ℝ) : Dth1Iter 0 f = f := rfl
@[simp] theorem Dth1Iter_succ (n : ℕ) (f : ℝ → ℝ) :
    Dth1Iter (n + 1) f = Dth1 (Dth1Iter n f) := rfl

end Work.Elliptic
