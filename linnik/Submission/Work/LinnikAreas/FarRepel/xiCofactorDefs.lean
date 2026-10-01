import Mathlib
import Submission.Work.LinnikAreas.DhK.XiAux

/-!
# `Work.LinnikAreas.FarRepel.xiCofactorDefs`

Vocabulary for the cofactor ("truncation error") input of the partial-fraction expansion of the
`k`-th derivative of `(Ξ'/Ξ)`.

At a good radius `T` (no zero of `Ξ` within `1/(xiL A)²` of the circle `|z| = T`) the entire
completion `Ξ` factors on a disc slightly larger than `B(0,T)` as

`Ξ z = (∏ᶠ_{‖u‖ ≤ T} (z - u)^{d_T u}) · g z`,

with `g` analytic and non-vanishing on that disc.  `XiCofactorBound A T zc gc` records the
existence of such a cofactor `g` together with the logarithmic bound
`log ‖g w‖ ≤ M0` on `B(0,T)`, the origin bound `|log ‖g 0‖| ≤ M0`, and the shape
`M0 ≤ (4·gc + 20·zc + |log ‖Ξ 0‖| + 1)·(A·(xiL A)² + 1)` of `M0`.  The parameters `zc`, `gc`
are the counting and growth constants for `Ξ` (`DhK.Xi_zeroCount_L`, `DhK.Xi_growth_L`), passed
through so that the final `M0`-arithmetic sees them explicitly.

This is the exact analogue of the `P₃` input
`Commons.NumberTheory.Linnik.pf_cofactor_logbound`, with `Λ := DhK.Xi`, `L_N N A := xiL A` and
`pfP N χ T z := ∏ᶠ u, (z - u)^{divisor Ξ (closedBall 0 T) u}`.
-/

open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas.FarRepel

/-- The cofactor data for `Ξ = (∏_{‖u‖≤T}(z-u)^{d_T u})·g` at the radius `T`: existence of `g`
and of the logarithmic bound `M0`, with `M0` of the prescribed shape in terms of the counting and
growth constants `zc`, `gc` and of `A`. -/
def XiCofactorBound (A T zc gc : ℝ) : Prop :=
  ∃ (g : ℂ → ℂ) (M0 : ℝ), 0 ≤ M0 ∧
    AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) T) ∧
    (∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) T → g w ≠ 0) ∧
    (∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) T → Work.LinnikAreas.DhK.Xi z =
      (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
        (Metric.closedBall (0 : ℂ) T) u)) * g z) ∧
    (∃ ε : ℝ, 0 < ε ∧ AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) (T + ε)) ∧
      (∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) (T + ε) → Work.LinnikAreas.DhK.Xi z =
        (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall (0 : ℂ) T) u)) * g z)) ∧
    (∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) T → Real.log ‖g w‖ ≤ M0) ∧
    |Real.log ‖g 0‖| ≤ M0 ∧
    M0 ≤ (4 * gc + 20 * zc + |Real.log ‖Work.LinnikAreas.DhK.Xi 0‖| + 1) *
      (A * (Work.LinnikAreas.DhK.xiL A) ^ 2 + 1)

end Work.LinnikAreas.FarRepel
