import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved
import Submission.Work.FTS_RegExport.RXA1.integrableOn_pth_mixed_sq_sin_C4
import Submission.Work.FTS_RegExport.THL.mixed_slice_pointwise_le_noTrace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `THL.angular_L2_noTrace` — the trace-free angular `L²` bound at fixed `z`

`angular_L2_noTrace`: for `0 < β ≤ 1` and a `C⁴` datum `f` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` which is honestly in `ℋ⁴` (**no** boundary-trace hypothesis),

  `∫_{Iθ} sin(2σ)^{-γ} (D_θ f(z,σ))² dσ ≤ 5 · z³/(1+z)⁴ · |f|²_{ℋ⁴}`,  `γ = gam β`,

together with integrability of the angular integrand.

This is leaf A2 of `THL.Leaves` ("copy `RXA1w.mixed_slice_pointwise_le` with
`RXA1w.agmonZ_weight` replaced by `RXT.Slots.v2_agmonZ_noDecay`").  The two steps are:

* **the a.e. slice bound** (`THL.mixed_slice_pointwise_le_noTrace`, the trace-free sibling of
  `RXA1w.mixed_slice_pointwise_le`): for almost every angle, the weighted `θ`-derivative at
  the slot `(b,a) = (0,0)` is dominated by `5 z³/(1+z)⁴ · ∫_s HkIntegrand β 4 f (s,σ)`.  The
  radial Agmon inequality is applied there without any decay hypothesis, and both of its
  energy slots are mixed slots of the nonnegative `ℋ⁴`-integrand;

* **integration in `σ`** (`C4.HkSqSwap_C4`, Tonelli for that nonnegative integrand): the
  `σ`-integral of `∫_s HkIntegrand β 4 f (s,σ)` is exactly `HkSq β 4 f` and is integrable as a
  function of `σ`, so `integral_mono_of_nonneg` applies.

The first conjunct (integrability of `sin(2σ)^{-γ} (D_θf(z,σ))²` on `Iθ`) is
`RXA1.integrableOn_pth_mixed_sq_sin_C4` at `(b,a) = (0,0)` — where the plain `θ`-derivative
carries the weight `sin(2σ)^{2-γ} = sin(2σ)² · sin(2σ)^{-γ}` — transported along the a.e.
identity `D_θ f = sin(2σ) ∂_θ f`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.THL

theorem angular_L2_noTrace {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun σ => Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed 0 1 f z σ) ^ 2) Work.Spaces.Iθ ∧
      ∫ σ in Work.Spaces.Iθ, Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed 0 1 f z σ) ^ 2
        ≤ 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by
  -- ## The first conjunct: integrability of the weighted angular slice at the slot `(0,1)`.
  have hint : MeasureTheory.IntegrableOn (fun σ => Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
      * (Work.Spaces.mixed 0 1 f z σ) ^ 2) Work.Spaces.Iθ := by
    refine (Work.FTS_RegExport.RXA1.integrableOn_pth_mixed_sq_sin_C4 hβ hβ1 h4 hmem 0 0
      (by omega) hz).congr ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    have hs : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hD : Work.Spaces.mixed 0 1 f z σ = Real.sin (2 * σ) * Work.Spaces.pth f z σ := rfl
    have hsplit : Real.sin (2 * σ) ^ (2 - Work.Spaces.gam β)
        = Real.sin (2 * σ) ^ (2 : ℝ) * Real.sin (2 * σ) ^ (-(Work.Spaces.gam β)) := by
      rw [show (2 : ℝ) - Work.Spaces.gam β = 2 + (-(Work.Spaces.gam β)) by ring,
        Real.rpow_add hs]
    rw [hD, mul_pow, hsplit]
    simp only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero, Real.rpow_two]
    ring
  -- ## The second conjunct: integrate the a.e. slice bound over the angle.
  obtain ⟨hswap, hTint, -⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  have hslice := mixed_slice_pointwise_le_noTrace hβ h4 hmem 0 0 (by omega) hz
  have hrhs : MeasureTheory.Integrable (fun σ => 5 * (z ^ 3 / (1 + z) ^ 4)
      * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hTint.const_mul _
  have hmono := integral_mono_of_nonneg
    (ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
      mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσ) _) (sq_nonneg _))
    hrhs hslice
  have hIntegral : (∫ σ in Work.Spaces.Iθ, Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed 0 1 f z σ) ^ 2)
      ≤ 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by
    calc (∫ σ in Work.Spaces.Iθ, Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed 0 1 f z σ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := hmono
      _ = 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
                Work.Spaces.HkIntegrand β 4 f s σ) := by
          rw [MeasureTheory.integral_const_mul]
      _ = 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by rw [hswap]
  exact ⟨hint, hIntegral⟩

end Work.FTS_RegExport.THL
