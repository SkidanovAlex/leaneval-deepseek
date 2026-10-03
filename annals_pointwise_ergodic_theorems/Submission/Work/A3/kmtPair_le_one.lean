import Mathlib
import Submission.Work.A3.HausdorffYoungDefs
import Submission.Port.Aesm

/-!
# The `(ℓ¹, L¹)` endpoint estimate for the Hausdorff--Young pairing

The bilinear pairing `kmtPair s u v = ∫₀¹ (∑_{x ∈ s} u x · e(-xθ)) v(θ) dθ` of
`HausdorffYoungDefs` satisfies the elementary `(ℓ¹, L¹)` bound

`‖kmtPair s u v‖ ≤ ‖u‖_{ℓ¹(ℤ)} · ‖v‖_{L¹([0,1])}`.

This is the `p = 1` endpoint of the Hausdorff--Young inequality: the pointwise bound
`‖∑_{x ∈ s} u x · e(-xθ)‖ ≤ ∑_{x ∈ s} ‖u x‖ ≤ ‖u‖_{ℓ¹}` (`enorm_kmtSum_le`), the triangle
inequality for the Bochner integral (`enorm_integral_le_lintegral_enorm`) and the finiteness of `s`
(`ENNReal.sum_le_tsum` applied to the counting measure on `ℤ`).

The estimate is stated for *arbitrary* `v`; the guard in the definition of `kmtPair`
(non-a.e.-measurable `v` gives `0`) together with the bound `ENNReal.sum_le_tsum` — which needs no
hypothesis on `u` at all, because the `ℓ¹` norm is the `tsum` over all of `ℤ` — makes the
inequality hold unconditionally.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.A3

theorem kmtPair_le_one (s : Finset ℤ) (u : ℤ → ℂ) (v : ℝ → ℂ) : enorm (Work.A3.kmtPair s u v) ≤ MeasureTheory.eLpNorm u 1 MeasureTheory.Measure.count * MeasureTheory.eLpNorm v 1 Work.A3.kmtNu := by
  by_cases hv : AEMeasurable v Work.A3.kmtNu
  · rw [Work.A3.kmtPair_of_aemeasurable hv]
    have hbound : (∑ x ∈ s, ‖u x‖ₑ) ≤ MeasureTheory.eLpNorm u 1 MeasureTheory.Measure.count := by
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), MeasureTheory.lintegral_count]
      exact ENNReal.sum_le_tsum s
    calc ‖∫ θ, Work.A3.kmtSum s u θ * v θ ∂Work.A3.kmtNu‖ₑ
        ≤ ∫⁻ θ, ‖Work.A3.kmtSum s u θ * v θ‖ₑ ∂Work.A3.kmtNu := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ θ, ‖Work.A3.kmtSum s u θ‖ₑ * ‖v θ‖ₑ ∂Work.A3.kmtNu := by
            simp only [enorm_mul]
      _ ≤ ∫⁻ θ, (∑ x ∈ s, ‖u x‖ₑ) * ‖v θ‖ₑ ∂Work.A3.kmtNu := by
            refine lintegral_mono fun θ => ?_
            exact mul_le_mul_left (Work.A3.enorm_kmtSum_le s u θ) _
      _ = (∑ x ∈ s, ‖u x‖ₑ) * MeasureTheory.eLpNorm v 1 Work.A3.kmtNu := by
            rw [lintegral_const_mul'' _ hv.enorm, MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
      _ ≤ MeasureTheory.eLpNorm u 1 MeasureTheory.Measure.count * MeasureTheory.eLpNorm v 1 Work.A3.kmtNu :=
            mul_le_mul_left hbound _
  · rw [Work.A3.kmtPair_of_not_aemeasurable hv]
    simp

end Work.A3
