import Mathlib
import Submission.Work.Mostow.VolDefs

/-!
# `volH_measure_facts`

Basic measure-theoretic regularity of the hyperbolic volume `volH n`, which is
`(volume : Measure (E n)).withDensity (fun u => ofReal (tpart u)⁻¹)` with `tpart u ≥ 1`:

* `IsFiniteMeasureOnCompacts` — the density is at most `1`, so `volH n ≤ volume`, and Lebesgue
  measure on `E n` is finite on compacta;
* `SigmaFinite` — `volH n` is the `withDensity` of a σ-finite measure by an everywhere finite
  density;
* `IsOpenPosMeasure` — this is `Work.Mostow.volHPosOpen` from `VolDefs`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

variable {n : ℕ}

/-- The density `(tpart u)⁻¹` of hyperbolic volume is everywhere at most `1`, because
`tpart u = √(1+‖u‖²) ≥ 1`. -/
theorem hdens_le_one (u : E n) : hdens u ≤ 1 := by
  rw [hdens, ENNReal.ofReal_le_one]
  exact inv_le_one_of_one_le₀ (one_le_tpart_VolDefs u)

/-- The density of hyperbolic volume is everywhere finite. -/
theorem hdens_ne_top (u : E n) : hdens u ≠ ⊤ := by
  rw [hdens]; exact ENNReal.ofReal_ne_top

/-- Hyperbolic volume is dominated by Lebesgue measure in the chart. -/
theorem volH_le_volume (n : ℕ) : volH n ≤ (volume : Measure (E n)) := by
  have h : volH n ≤ (volume : Measure (E n)).withDensity (1 : E n → ℝ≥0∞) := by
    rw [volH_def]
    exact withDensity_mono (ae_of_all _ (fun u => hdens_le_one u))
  rwa [withDensity_one] at h

-- `volH n = (volume : Measure (E n)).withDensity (fun u => ENNReal.ofReal (tpart u)⁻¹)`; `tpart u ≥ 1`
-- (see `Submission.Work.Mostow.VolDefs`: `volH_def`, `volHApply`, `volHPosOpen`, `hdens_pos`).
theorem volH_measure_facts (n : ℕ) :
    MeasureTheory.IsFiniteMeasureOnCompacts (Submission.Mostow.volH n) ∧
    MeasureTheory.SigmaFinite (Submission.Mostow.volH n) ∧
    MeasureTheory.Measure.IsOpenPosMeasure (Submission.Mostow.volH n) := by
  refine ⟨?_, ?_, ?_⟩
  · -- finite on compacta, since `volH n ≤ volume` and Lebesgue measure is finite on compacta
    exact ⟨fun K hK => lt_of_le_of_lt (volH_le_volume n K) hK.measure_lt_top⟩
  · -- σ-finite, being a `withDensity` of σ-finite Lebesgue measure by a finite density
    rw [volH_def]
    exact SigmaFinite.withDensity_of_ne_top' (μ := (volume : Measure (E n)))
      (fun u => hdens_ne_top u)
  · -- positive on nonempty open sets, which is `volHPosOpen`
    exact ⟨fun U hU hne => ne_of_gt (volHPosOpen n hU hne)⟩

end

end Work.Mostow
