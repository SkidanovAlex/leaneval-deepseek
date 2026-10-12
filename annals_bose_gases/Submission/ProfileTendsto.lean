import ChallengeDeps
import Submission.RadialRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Decay of a radial profile at infinity

Goal theorem (assigned sub-lemma, same statement as in `Submission.ProfileEq1D`):

    radialProfile_tendsto_zero {w : ℝ³ → ℝ} (hrad : IsRadial w)
      (hwlim : Tendsto w (cocompact ℝ³) (𝓝 0)) :
      Tendsto (fun r : ℝ => radialProfile w r) atTop (𝓝 0)

`radialProfile w r := w (r • radU0)` (`Submission.RadialRep`), with
`radU0` a unit vector.  As `r → ∞` along the positive reals, the point
`r • radU0 ∈ ℝ³` escapes every compact set (its norm is `r`), so
`w (r • radU0) → 0`.

## Proof route (recorded for the implementer)

Prove `Tendsto (fun r => w (r • radU0)) atTop (𝓝 0)` from
`hwlim : Tendsto w (cocompact ℝ³) (𝓝 0)` by composing with the map
`s : ℝ → ℝ³, s r := r • radU0`:

1. Show the map `s` is *cocompact-tending*: `Tendsto s atTop (cocompact ℝ³)`.
   In the finite-dimensional space `ℝ³` the cocompact filter equals the
   cobounded filter (`Metric.cobounded_eq_cocompact`), and a function
   tends to the cobounded filter of a normed group iff its norm tends to
   `atTop` (`tendsto_norm_atTop_iff_cobounded`).  Here
   `‖r • radU0‖ = |r|` (`norm_smul_radU0`), and `|r| → ∞` as `r → ∞`
   (`tendsto_abs_atTop_atTop`).

2. Since `hwlim : Tendsto w (cocompact ℝ³) (𝓝 0)`, composing with the
   cocompact-tending map `s` (`Filter.Tendsto.comp`) gives
   `Tendsto (w ∘ s) atTop (𝓝 0)`, i.e. exactly
   `Tendsto (fun r => w (r • radU0)) atTop (𝓝 0)` (definitional, since
   `radialProfile w r` unfolds to `w (r • radU0)`).
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The map `r ↦ r • radU0` sends `atTop` on `ℝ` to the cocompact filter
on `ℝ³`: as `r → ∞` the point `r • radU0` escapes every compact set. -/
lemma smul_radU0_tendsto_cocompact_atTop :
    Tendsto (fun r : ℝ => r • radU0) atTop (cocompact ℝ³) := by
  rw [← Metric.cobounded_eq_cocompact (α := ℝ³)]
  rw [← tendsto_norm_atTop_iff_cobounded]
  have hcongr : (fun r : ℝ => ‖r • radU0‖) =ᶠ[atTop] (fun r : ℝ => |r|) := by
    filter_upwards with r
    rw [norm_smul_radU0]
  rw [Filter.tendsto_congr' hcongr]
  exact tendsto_abs_atTop_atTop (G := ℝ)

/-- Decay of the radial profile at infinity: if `w x → 0` as `‖x‖ → ∞` and
`w` is radial, then `f(r) = w (r • radU0)` tends to `0` as `r → ∞`. -/
theorem radialProfile_tendsto_zero {w : ℝ³ → ℝ} (hrad : IsRadial w)
    (hwlim : Tendsto w (cocompact ℝ³) (𝓝 0)) :
    Tendsto (fun r : ℝ => radialProfile w r) atTop (𝓝 0) := by
  change Tendsto (fun r : ℝ => w (r • radU0)) atTop (𝓝 0)
  exact hwlim.comp smul_radU0_tendsto_cocompact_atTop

end Submission.BoseGases
