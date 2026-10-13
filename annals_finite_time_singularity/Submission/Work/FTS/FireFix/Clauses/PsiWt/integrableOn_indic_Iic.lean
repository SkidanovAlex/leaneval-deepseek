import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.FireFix.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.PsiWt

/-- The indicator of the half-plane `{q | q.1 ≤ L}` is integrable on the strip
`(0,∞) × (-π/2, π/2)`: its support there is contained in the rectangle
`(0, L] × (-π/2, π/2)`, which has finite Lebesgue measure. -/
theorem integrableOn_indic_Iic {L : ℝ} (hL : 0 ≤ L) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ => (if q.1 ≤ L then (1 : ℝ) else 0))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  set s : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) with hs
  have hsmeas : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  -- `u` is the support of the integrand inside the strip `s`.
  set u : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.1 ≤ L} ∩ s with hu
  have humeas : MeasurableSet u := (measurableSet_Iic.preimage measurable_fst).inter hsmeas
  -- On `s`, the integrand agrees with the indicator of `u`.
  have hEq : Set.EqOn (fun q : ℝ × ℝ => (if q.1 ≤ L then (1 : ℝ) else 0))
      (u.indicator (fun _ => (1 : ℝ))) s := by
    intro q hq
    have hmem : (q ∈ u) ↔ q.1 ≤ L := by
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, hq⟩
    simp only [Set.indicator_apply]
    by_cases h : q.1 ≤ L
    · simp [h, hmem.mpr h]
    · simp [h, hmem]
  -- `u` is contained in a rectangle of finite measure.
  have hfin : MeasureTheory.volume u < ⊤ := by
    have hsub : u ⊆ Set.Ioc 0 L ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      rintro ⟨x, y⟩ ⟨hx, hxs⟩
      simp only [hs, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hxs
      exact ⟨⟨hxs.1, hx⟩, hxs.2⟩
    calc MeasureTheory.volume u
        ≤ MeasureTheory.volume (Set.Ioc 0 L ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
          MeasureTheory.measure_mono hsub
      _ = MeasureTheory.volume (Set.Ioc (0 : ℝ) L)
            * MeasureTheory.volume (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
          rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
      _ = ENNReal.ofReal (L - 0) * ENNReal.ofReal (Real.pi / 2 - -(Real.pi / 2)) := by
          rw [Real.volume_Ioc, Real.volume_Ioo]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- The indicator of `u` is integrable on `s`, since `volume (u ∩ s) < ∞`.
  have hint : MeasureTheory.IntegrableOn (u.indicator (fun _ => (1 : ℝ))) s := by
    rw [MeasureTheory.integrableOn_indicator_iff humeas]
    have hle : MeasureTheory.volume (u ∩ s) ≤ MeasureTheory.volume u :=
      MeasureTheory.measure_mono Set.inter_subset_left
    exact MeasureTheory.integrableOn_const (ne_top_of_lt (lt_of_le_of_lt hle hfin))
  exact (MeasureTheory.integrableOn_congr_fun hEq hsmeas).2 hint

end Work.FTS.FireFix.Clauses.PsiWt
