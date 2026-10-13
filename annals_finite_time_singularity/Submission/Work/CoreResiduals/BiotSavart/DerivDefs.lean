/-
# `Work.CoreResiduals.BiotSavart.DerivDefs` — the derivative of the Biot–Savart field

This file fixes the two objects used by the `C¹`-regularity proof of the Biot–Savart field
`Work.LWP.biotSavart ω` for a vorticity `ω` that is bounded, supported in `closedBall 0 R`,
ae-strongly-measurable and Hölder of exponent `c > 0`.

* `bsField ω ρ x = ∫_{a ∈ B(0,ρ)} ω a ×₃ kf (x - a)` — the *un-normalised* Biot–Savart field,
  written as an integral over a fixed ball `B(0,ρ)` containing the support of `ω`.  For
  `R + ‖x‖ ≤ ρ` one has `4π • biotSavart ω x = bsField ω ρ x`.
* `bsDerivCLM ω ρ x` — the candidate Fréchet derivative of `bsField ω ·` at `x`,
  `h ↦ ∫_{a ∈ B(0,ρ)} (ω a - ω x) ×₃ (kDerivCLM (x-a)) h + (4π/3) • (ω x ×₃ h)`.

The singular term `a = x` is cured by the odd-kernel cancellation: the *shape* term
`(4π/3) • (ω x ×₃ h)` is exactly the contribution of `ω x ×₃ ∫_{B(0,ρ)}(kf(x+h-a) - kf(x-a)) da`,
which equals `ω x ×₃ ((4π/3) h)` — the derivative of the ball potential `z ↦ ∫_{B(z,ρ)} kf`
(proved as `Work.CoreResiduals.BiotSavart.kf_ball_integral`).
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-- `ℝ³` (definitionally `Work.LWP.R3`). -/
abbrev R3 : Type := Work.LWP.R3

/-- The un-normalised Biot–Savart field, as an integral of the kernel
`a ↦ ω a ×₃ kf (x - a)` over the fixed ball `B(0,ρ)`:
`4π • biotSavart ω x = bsField ω ρ x` as soon as `R + ‖x‖ ≤ ρ` (cf. `biotSavart_ball_integral`). -/
noncomputable def bsField (ω : R3 → R3) (ρ : ℝ) (x : R3) : R3 :=
  ∫ a in Metric.ball (0 : R3) ρ, crossL (ω a) (kf (x - a))

/-- The candidate Fréchet derivative of `bsField ω ρ` at `x`: the Bochner integral of the CLMs
`(crossL (ω a - ω x)).comp (kDerivCLM (x - a))` plus the *shape* term `(4π/3) • crossL (ω x)`.

The subtracted `ω x` makes the integrand absolutely integrable (`‖·‖ ≤ C‖x-a‖^{c-3}`), and the
shape term accounts for the derivative of the ball potential `z ↦ ∫_{B(0,ρ)} kf (z - a) da`
(`kf_ball_integral`). -/
noncomputable def bsDerivCLM (ω : R3 → R3) (ρ : ℝ) (x : R3) : R3 →L[ℝ] R3 :=
  (∫ a in Metric.ball (0 : R3) ρ, (crossL (ω a - ω x)).comp (kDerivCLM (x - a)))
    + (4 * Real.pi / 3) • crossL (ω x)

end Work.CoreResiduals.BiotSavart
