/-
# Shared definitions for `Eztheta1_eq_HkSq_one`

The energy `E_{z,θ}¹` of Elgindi's paper is the sum of the squares of the three
weighted first-order derivatives
`f·w/sin(2θ)^{η/2}`, `D_zf·w/sin(2θ)^{η/2}` and `D_θf·W`, which are exactly the three
summands of `HkIntegrand α 1 f`.  This file fixes the names used both by the main proof
and by the delegated lemmas:

* `I2Mem A` — the iterated integral of `A` over the quadrant is honest;
* `U0 f`, `U1 f` — the `D_z⁰`/`D_z¹` summands of `HkIntegrand α 1 f`;
* `U2 α f` — the `D_θ` summand of `HkIntegrand α 1 f`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Spaces.ProductTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- Honesty of an iterated integral over the quadrant `[0,∞) × [0,π/2]`: every angular
slice is integrable and the resulting function of `z` is integrable on `[0,∞)`. -/
def I2Mem (A : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Spaces.Iz, IntegrableOn (fun θ => A z θ) Spaces.Iθ) ∧
    IntegrableOn (fun z => ∫ θ in Spaces.Iθ, A z θ) Spaces.Iz

/-- `L2Mem g` is exactly the honesty of the iterated integral of `g²`. -/
theorem I2Mem_sq_iff (g : ℝ → ℝ → ℝ) :
    I2Mem (fun z θ => (g z θ) ^ 2) ↔ Spaces.L2Mem g := Iff.rfl

/-- The `D_z⁰f` summand of `HkIntegrand α 1 f`. -/
def U0 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.DzIter 0 f z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))

/-- The `D_z¹f` summand of `HkIntegrand α 1 f`. -/
def U1 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.DzIter 1 f z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))

/-- The `D_θf` summand of `HkIntegrand α 1 f`. -/
def U2 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.mixed 0 1 f z θ * Spaces.Wt α z θ

end Work.Coercivity
