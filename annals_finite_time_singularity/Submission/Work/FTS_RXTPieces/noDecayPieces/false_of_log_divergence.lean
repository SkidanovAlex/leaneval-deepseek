import Mathlib.Analysis.SpecialFunctions.NonIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.noDecayPieces

-- the a.e. nonnegativity hypothesis is not needed: `hg` already gives pointwise positivity
-- on `(z,∞)`, so the proof below does not consume it
set_option linter.unusedVariables false in
theorem false_of_log_divergence {g : ℝ → ℝ} {z c : ℝ}
    (hz : 0 < z) (hc : 0 < c)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] g)
    (hg : ∀ x, z ≤ x → c / x ≤ g x) : False := by
  -- `g` is integrable on `(z,∞)`
  have hgz : MeasureTheory.IntegrableOn g (Set.Ioi z) :=
    hint.mono_set (Set.Ioi_subset_Ioi hz.le)
  -- hence so is the larger function `x ↦ c⁻¹ * g x`
  have h1 : MeasureTheory.IntegrableOn (fun x : ℝ => c⁻¹ * g x) (Set.Ioi z) :=
    MeasureTheory.Integrable.const_mul hgz c⁻¹
  -- comparing with `x ↦ x⁻¹ ≤ c⁻¹ * g x` on `(z,∞)` gives integrability of `x ↦ x⁻¹`
  have h2 : MeasureTheory.IntegrableOn (fun x : ℝ => x⁻¹) (Set.Ioi z) := by
    refine MeasureTheory.Integrable.mono' h1 measurable_inv.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hz.trans hx
    have hle : c / x ≤ g x := hg x hx.le
    have hcoef : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
    have hkey : c⁻¹ * (c / x) = x⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hx0, ← hkey]
    exact mul_le_mul_of_nonneg_left hle hcoef.le
  exact not_integrableOn_Ioi_inv h2

end Work.FTS_RXTPieces.noDecayPieces
