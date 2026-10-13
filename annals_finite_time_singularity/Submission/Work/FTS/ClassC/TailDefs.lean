/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial tail weight of the `ClassC` decay lemmas

This module fixes the vocabulary used by the decay lemmas
`Work.FTS.ClassC.fstar_tendsto_atTop_zero_of_classC` (and its `Gsing` sibling): the
**radial tail lintegral**

  `zTail g θ = ∫⁻_{s ∈ Iz} ofReal ((D_z g(s,θ))² · w(s)²)`,

together with its real part `zTailR g θ = (zTail g θ).toReal`.

Why this object.  For a fixed angle `θ ∈ (0,π/2)` the one-dimensional (radial) Hardy
inequality `Work.FTS.H2.HQ.HardyZQ` bounds the *value* `(g z θ)²` uniformly in `z` by the
weighted `L²`-mass of `D_z g(·,θ)`, i.e. by the (real part of the) tail integral above.
The finiteness of `zTail` for a.e. `θ` follows from `HkMem` (Tonelli), and
`θ ↦ zTailR g θ` is then an integrable dominating function for the family
`θ ↦ g z θ · sinθ cos²θ` of the dominated-convergence argument in
`fstar_tendsto_atTop_zero_of_classC`.

Note `w 0 = 0` in Lean's totalised division, so the point `s = 0` contributes nothing to
`zTail`.
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- The radial tail lintegral of `g` at the angle `θ`:
`zTail g θ = ∫⁻_{s ∈ [0,∞)} ofReal ((D_z g(s,θ))² · w(s)²)`. -/
def zTail (g : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.Dz g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)

/-- The real part of the radial tail lintegral.  It is the honest value of `zTail g θ`
whenever the latter is finite, and `0` otherwise. -/
def zTailR (g : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ := ENNReal.toReal (zTail g θ)

@[simp] theorem zTailR_eq_toReal (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    zTailR g θ = ENNReal.toReal (zTail g θ) := rfl

theorem zTailR_nonneg (g : ℝ → ℝ → ℝ) (θ : ℝ) : 0 ≤ zTailR g θ :=
  ENNReal.toReal_nonneg

/-- The tail lintegral is the `∫⁻` of a nonnegative function, so it vanishes only if the
integrand does; in particular it is monotone in the obvious way. -/
theorem zTail_eq_lintegral (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    zTail g θ = MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
      (fun s => ENNReal.ofReal ((Work.Spaces.Dz g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)) := rfl

end Work.FTS.ClassC
