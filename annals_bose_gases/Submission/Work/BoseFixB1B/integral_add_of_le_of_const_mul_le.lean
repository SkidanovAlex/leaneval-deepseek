import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseFixB1B

/-- Suppose `0 ≤ᵐ f`, `h ≤ᵐ f` and `c * f ≤ᵐ h` for a positive constant `c`, with `f` and `h`
a.e. strongly measurable.  Then `f`, `h` and `f + h` are integrable simultaneously (the
sandwich forces it), so the Bochner integral is additive for this pair — either all three
functions are integrable and `integral_add` applies, or none is and every integral is `0`
by definition. -/
lemma integral_add_of_le_of_const_mul_le {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f h : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hfA : MeasureTheory.AEStronglyMeasurable f μ) (hhA : MeasureTheory.AEStronglyMeasurable h μ)
    (hf : 0 ≤ᵐ[μ] f) (hfh : h ≤ᵐ[μ] f) (hch : ∀ᵐ x ∂μ, c * f x ≤ h x) :
    ∫ x, (f x + h x) ∂μ = ∫ x, f x ∂μ + ∫ x, h x ∂μ := by
  -- `h` is nonnegative a.e. since `h ≥ c * f ≥ 0`.
  have h0h : ∀ᵐ x ∂μ, 0 ≤ h x := by
    filter_upwards [hf, hch] with x hx hcx
    exact le_trans (mul_nonneg hc.le hx) hcx
  -- hence `‖h‖ ≤ f` a.e.
  have hhnorm : ∀ᵐ x ∂μ, ‖h x‖ ≤ f x := by
    filter_upwards [h0h, hfh] with x hx0 hxle
    rw [Real.norm_of_nonneg hx0]
    exact hxle
  -- `f` integrable ⟹ `h` integrable, and conversely.
  have hhi_of_hfi : MeasureTheory.Integrable f μ → MeasureTheory.Integrable h μ :=
    fun hfi => MeasureTheory.Integrable.mono' hfi hhA hhnorm
  have hfi_of_hhi : MeasureTheory.Integrable h μ → MeasureTheory.Integrable f μ := by
    intro hhi
    have hcint : MeasureTheory.Integrable (fun x => c⁻¹ * h x) μ := hhi.const_mul c⁻¹
    refine MeasureTheory.Integrable.mono' hcint hfA ?_
    filter_upwards [hf, hch] with x hfx hcx
    rw [Real.norm_of_nonneg hfx]
    have : c⁻¹ * (c * f x) ≤ c⁻¹ * h x :=
      mul_le_mul_of_nonneg_left hcx (inv_nonneg.mpr hc.le)
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] at this
  -- `f + h` integrable ⟹ `f` integrable, as `0 ≤ f ≤ f + h`.
  have hfi_of_hfhi : MeasureTheory.Integrable (fun x => f x + h x) μ →
      MeasureTheory.Integrable f μ := by
    intro hfh_int
    refine MeasureTheory.Integrable.mono' hfh_int hfA ?_
    filter_upwards [hf, h0h] with x hfx hhx
    rw [Real.norm_of_nonneg hfx]
    exact le_add_of_nonneg_right hhx
  by_cases hfi : MeasureTheory.Integrable f μ
  · -- everything is integrable: additivity of the Bochner integral.
    exact MeasureTheory.integral_add hfi (hhi_of_hfi hfi)
  · -- nothing is integrable: all three integrals vanish by definition.
    rw [MeasureTheory.integral_undef (fun hh => hfi (hfi_of_hfhi hh)),
      MeasureTheory.integral_undef hfi,
      MeasureTheory.integral_undef (fun hh => hfi (hfi_of_hhi hh)), add_zero]

end Work.BoseFixB1B
