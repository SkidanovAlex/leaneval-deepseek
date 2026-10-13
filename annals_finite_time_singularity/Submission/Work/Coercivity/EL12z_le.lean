import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.EL12z_ae_slice
import Submission.Work.Coercivity.EL12z_Kd
import Submission.Work.Coercivity.EL12z_weight
import Submission.Work.Coercivity.EL12z_hardy

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

/-- **The Hardy inequality of the paper's `Lemma HardyWeight` in the form used by the
coercivity chain**: `|z⁻¹ L₁₂(f)|²_{L²_z} ≤ 16 |f w|²_{L²}`.

The chain of estimates is
`∫ (L₁₂ f)²/z² ≤ 4 ∫ (L₁₂dens)² ≤ 4·3 ∫ (∫_θ f²)/z² ≤ 12 |f w|²_{L²}`,
where the first step is the Hardy inequality (integration by parts, using that
`∂_z L₁₂(f) = -L₁₂dens(f)` and that the boundary terms `(L₁₂ f)²/z` vanish at `0⁺` and at
`∞`), the second is Cauchy–Schwarz in `θ` against `∫_θ K² ≤ 3`, and the last one uses
`1/z² ≤ w z²`. -/
theorem EL12z_le (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    EL12z f ≤ 16 * Ef f := by
  -- almost everywhere integrability of the angular slices of `f²`, from `hfw`
  have hsl := EL12z_ae_slice f hfw
  -- finiteness of `∫ (L₁₂dens)²` and its `L¹` bound by `∫ (∫_θ f²)/z²`
  have hKd := EL12z_Kd f hf hsl
  -- the plain `1/z²` piece of `|f w|²` is bounded by `Ef f`
  have hw := EL12z_weight f hfw hsl
  -- the Hardy inequality `∫ (L₁₂ f)²/z² ≤ 4 ∫ (L₁₂dens)²`
  have hh := EL12z_hardy f hf hKd.1
  -- `Ef f ≥ 0`
  have hEf : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  -- `EL12z f = ∫_0^∞ (L₁₂ f)²/z²` (`{0}` is null and `(a/b)² = a²/b²`)
  have h1 : EL12z f = ∫ z in Set.Ioi (0 : ℝ), (L12f f z) ^ 2 / z ^ 2 := by
    rw [EL12z, L2Sqz, Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine integral_congr_ae ?_
    filter_upwards with z
    exact div_pow (L12f f z) z 2
  rw [h1]
  linarith [hh, hKd.2, hw, hEf]

end Work.Coercivity
