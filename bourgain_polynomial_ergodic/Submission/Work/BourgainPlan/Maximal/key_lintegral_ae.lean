import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_q_strong_p_top

namespace Work.BourgainPlan.Maximal

open MeasureTheory Measure Filter Set
open scoped ENNReal

/-- `Commons.Analysis.MeasureTheory.key_lintegral` (in
`Submission/Commons/Analysis/MeasureTheory/marcinkiewicz_weak_q_strong_p_top.lean`) with the
measurability hypothesis weakened from `Measurable v` to `AEMeasurable v μ`.  The proof takes a
measurable representative `v'` of `v` (`AEMeasurable.mk`), clips it to `max v' 0` so that it is
nonnegative everywhere (needed by `key_lintegral`), applies `key_lintegral` to the clip, and
transports both sides along the a.e. equality `v =ᵐ[μ] v'`; no measurability of `v` itself is
used elsewhere. -/
theorem key_lintegral_ae {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.SFinite μ]
    {v : α → ℝ} (hvm : AEMeasurable v μ) (hv : ∀ x, 0 ≤ v x)
    {c : ℝ} (hc : 0 < c) {q r : ℝ} (hq : 0 ≤ q) (hr : -1 < r) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (v x)}
            (fun x => ENNReal.ofReal (v x) ^ q) x ∂μ)
      = ENNReal.ofReal ((2*c) ^ (r + 1) / (r + 1)) *
          ∫⁻ x, ENNReal.ofReal (v x) ^ (q + r + 1) ∂μ := by
  -- A measurable representative of `v`, truncated below at `0` so that it is nonnegative
  -- everywhere (it is a.e. equal to `v`, hence a.e. nonnegative).
  let w : α → ℝ := fun x => max 0 (hvm.mk v x)
  have hw_meas : Measurable w := measurable_const.max hvm.measurable_mk
  have hw_nonneg : ∀ x, 0 ≤ w x := fun x => le_max_left _ _
  have hae_w : v =ᵐ[μ] w := by
    filter_upwards [hvm.ae_eq_mk] with x hx
    show v x = max 0 (hvm.mk v x)
    rw [hx, max_eq_right (by rw [← hx]; exact hv x)]
  -- For each `t`, the two inner integrals agree, because `v` and `w` agree a.e.
  have hinner : ∀ t : ℝ,
      (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (v x)}
            (fun x => ENNReal.ofReal (v x) ^ q) x ∂μ)
      = (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (w x)}
            (fun x => ENNReal.ofReal (w x) ^ q) x ∂μ) := by
    intro t
    apply lintegral_congr_ae
    filter_upwards [hae_w] with x hx
    have hiff : (x ∈ {y : α | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (v y)})
        ↔ (x ∈ {y : α | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (w y)}) := by
      simp only [Set.mem_ofPred_eq]
      rw [hx]
    by_cases hxS : x ∈ {y : α | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (v y)}
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem (hiff.mp hxS)]
      simp only [hx]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem (fun h => hxS (hiff.mpr h))]
  have hL : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (v x)}
            (fun x => ENNReal.ofReal (v x) ^ q) x ∂μ))
      = (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (w x)}
            (fun x => ENNReal.ofReal (w x) ^ q) x ∂μ)) := by
    apply lintegral_congr
    intro t
    rw [hinner t]
  have hR : (∫⁻ x, ENNReal.ofReal (v x) ^ (q + r + 1) ∂μ)
      = (∫⁻ x, ENNReal.ofReal (w x) ^ (q + r + 1) ∂μ) := by
    apply lintegral_congr_ae
    filter_upwards [hae_w] with x hx
    rw [hx]
  rw [hL, hR]
  exact Commons.Analysis.MeasureTheory.key_lintegral hw_meas hw_nonneg hc hq hr

end Work.BourgainPlan.Maximal
