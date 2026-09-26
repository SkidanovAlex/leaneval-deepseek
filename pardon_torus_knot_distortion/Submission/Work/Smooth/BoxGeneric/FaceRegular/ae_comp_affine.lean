import Mathlib

namespace Work.Smooth.BoxGeneric.FaceRegular

/-- The Lebesgue measure on `ℝ` is (up to the constant `|b⁻¹|`) invariant under the affine
reparametrisation `s ↦ b * s + a` with `b ≠ 0`; in particular it preserves null sets, so an
almost-everywhere statement pulls back along it. -/
theorem ae_comp_affine {P : ℝ → Prop} {a b : ℝ} (hb : b ≠ 0) (h : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), P t) : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), P (b * s + a) := by
  rw [MeasureTheory.ae_iff] at h ⊢
  rw [show {s : ℝ | ¬ P (b * s + a)} =
      (fun s => b * s) ⁻¹' ((fun t => t + a) ⁻¹' {t : ℝ | ¬ P t}) from by ext s; simp]
  rw [Real.volume_preimage_mul_left hb, MeasureTheory.measure_preimage_add_right, h, mul_zero]

end Work.Smooth.BoxGeneric.FaceRegular
