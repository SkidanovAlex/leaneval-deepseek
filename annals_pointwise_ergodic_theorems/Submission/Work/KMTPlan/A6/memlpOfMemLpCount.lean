import Mathlib
import Submission.Work.Analysis.IonescuWainger.FourierZ
import Submission.Port.Aesm

namespace Work.KMTPlan.A6

open MeasureTheory ENNReal

/-- Elements of `L^p` on `ℤ` with respect to the counting measure are `ℓ^p` sequences.
The proof converts the `L^p` seminorm into the `ℓ^p` series via `lintegral_count`, then
extracts summability of the real series from finiteness of the `ℝ≥0∞`-valued series. -/
theorem memlpOfMemLpCount {p : ENNReal} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) {f : ℤ → ℂ} (hf : MeasureTheory.MemLp f p MeasureTheory.Measure.count) : Memℓp f p := by
  rw [memℓp_gen_iff (ENNReal.toReal_pos hp0 hptop)]
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hlt : ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂(Measure.count : Measure ℤ) < ⊤ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm) hp0 hptop).mp hf.eLpNorm_lt_top
  rw [lintegral_count] at hlt
  have hpoint : ∀ a : ℤ, ‖f a‖ₑ ^ p.toReal = ENNReal.ofReal (‖f a‖ ^ p.toReal) := by
    intro a
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt hp)]
  simp_rw [hpoint] at hlt
  have hnn : Summable (fun a : ℤ => (‖f a‖ ^ p.toReal).toNNReal) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa only [ENNReal.ofReal] using hlt.ne
  have := NNReal.summable_coe.2 hnn
  simpa only [Real.coe_toNNReal _ (Real.rpow_nonneg (norm_nonneg _) _)] using this

end Work.KMTPlan.A6
