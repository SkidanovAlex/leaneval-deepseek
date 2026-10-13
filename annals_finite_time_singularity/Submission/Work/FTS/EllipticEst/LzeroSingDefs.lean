/-
Copyright: work module for the Elgindi finite-time singularity project.

# The singular solution of `Lzero` at `θ = π/2` — definitions

`Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` (`Work.Elliptic.Lzero`) is the angular part of the
self-similar Biot–Savart operator.  On the open angular interval `(0, π/2)` it has an **ordinary
point at `θ = 0`** (the coefficients `tan θ`, `sec²θ` are analytic there) and a **regular
singular point at `θ = π/2`** (where `tan θ ~ 1/t`, `sec²θ ~ 1/t²`, `t = π/2 - θ`); the indicial
polynomial is `r(r-1) + r - 1 = r² - 1`, so the two exponents are `r = ±1`.

The hypothesis class of `Work.FTS.EllipticEst.l2etaWeakFts` prescribes only the *values*
`Ψ(·,0) = Ψ(·,π/2) = 0` and smoothness on the **open** quadrant, hence it admits functions
behaving like the `r = -1` branch, i.e. with a genuine pole `≍ c/t` at `θ = π/2`.  This module
introduces the two special solutions that every consumer of the "pole coefficient" needs:

* `LzeroReg  θ = sin 2θ` — the regular solution (`Lzero (sin 2θ) = 0`, analytic everywhere);
* `LzeroSing` — the singular solution, in the **explicit reduction-of-order form**

  `LzeroSing θ = sin (2θ) · ∫_{π/4}^{π/2-θ} ds / (sin s · sin(2s)²)`.

  (For `Lzero y = -y'' + (tan · y)' - 6y = 0` the Wronskian of two solutions satisfies
  `W' = (tan θ)·W`, i.e. `W = C/cos θ` — in particular `sin(2θ)·∂LzeroSing - ∂(sin 2θ)·LzeroSing
  = -1/cos θ` on `(0,π/2)`, the certificate that the two solutions carry the indicial weights
  `t^{±1}`; with `y₁ = sin 2θ` the second solution is `y₁ ∫ W/y₁² dθ`, which is the formula above
  up to the integration constant.)

The content of the two theorems below is proved in the companion modules
`Submission/Work/FTS/EllipticEst/LzeroSingODE.lean` (`LzeroSing` solves the equation on
`(0, π/2)`) and `Submission/Work/FTS/EllipticEst/LzeroSingPole.lean`
(`(π/2 - θ)·LzeroSing θ → -1/4` as `θ → π/2⁻`, i.e. `LzeroSing ~ -1/(4t)`); numerically verified
in `_singular_check.py` at the workspace root.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- The reduction-of-order weight `1/(sin s · sin(2s)²) = 1/(4 sin³s cos²s)` of the singular
solution of `Lzero` (`= W/y₁²` for the Wronskian `W = 1/cos` and `y₁ = sin 2θ`). -/
def LzeroSingIntegrand (s : ℝ) : ℝ := 1 / (Real.sin s * (Real.sin (2 * s)) ^ 2)

/-- The **singular solution of `Lzero` at `θ = π/2`**, in explicit reduction-of-order form:
`LzeroSing θ = sin(2θ) · ∫_{π/4}^{π/2-θ} ds/(sin s · sin(2s)²)`.  It satisfies `Lzero = 0` on
`(0, π/2)` and behaves like `-1/(4t)` as `t = π/2 - θ → 0⁺` (so `θ ↦ (π/2-θ)·LzeroSing θ → -1/4`).
It is the carrier of the `r = -1` indicial behaviour at the singular angular endpoint. -/
noncomputable def LzeroSing (θ : ℝ) : ℝ :=
  Real.sin (2 * θ) * ∫ s in (Real.pi / 4)..(Real.pi / 2 - θ), LzeroSingIntegrand s

/-- The **regular solution of `Lzero`**: `θ ↦ sin 2θ`. -/
def LzeroReg (θ : ℝ) : ℝ := Real.sin (2 * θ)

@[simp] theorem LzeroReg_apply (θ : ℝ) : LzeroReg θ = Real.sin (2 * θ) := rfl

theorem LzeroReg_zero : LzeroReg 0 = 0 := by
  simp [LzeroReg]

theorem LzeroReg_pi_half : LzeroReg (Real.pi / 2) = 0 := by
  rw [LzeroReg, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]

/-! ## The two Dirichlet values of the singular solution

The class of `Work.FTS.EllipticEst.l2etaWeakFts` prescribes the *values* `Ψ(·,0) = 0` and
`Ψ(·,π/2) = 0` (and smoothness only on the **open** quadrant), so a function may vanish at both
angular endpoints as a value while blowing up like `1/t` in the limit `θ → π/2⁻`.  `LzeroSing`
is exactly such a function: this is what makes the class genuinely bigger than the class of the
paper's estimates, and it is why the "pole coefficient" (the coefficient of `LzeroSing` in a
solution) is the right singular datum. -/

theorem LzeroSing_zero : LzeroSing 0 = 0 := by
  simp [LzeroSing]

theorem LzeroSing_pi_half : LzeroSing (Real.pi / 2) = 0 := by
  have h : 2 * (Real.pi / 2) = Real.pi := by ring
  simp [LzeroSing, h]

/-! ## `LzeroSing` in the vocabulary of the project

`Work.Elliptic.Lzero` is stated for two-variable functions; applied to the `z`-independent
extension `fun _ τ => LzeroSing τ` it is the one-variable expression of the companion modules.
This unfolding is definitional, and lets consumers (`Work.Elliptic.Lzero`, the pole-coefficient
split, the elliptic estimates) use `LzeroSingODE` directly. -/

theorem Lzero_LzeroSing_apply (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ τ => LzeroSing τ) z θ
      = -(deriv (deriv LzeroSing) θ)
        + deriv (fun τ => Real.tan τ * LzeroSing τ) θ - 6 * LzeroSing θ := rfl

end Work.FTS.EllipticEst
