import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

theorem not_integrableOn_of_le_const_on_Ioi {f : ℝ → ℝ} {a m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (hf : ∀ z ∈ Set.Ioi a, m ≤ f z) :
    ¬ MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  intro h
  -- `(a, ∞) ⊆ (0, ∞)`, so integrability transfers to `(a, ∞)`
  have hsub : Set.Ioi a ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi ha.le
  have hIa : MeasureTheory.IntegrableOn f (Set.Ioi a) := h.mono_set hsub
  -- finiteness of the lower Lebesgue integral of `‖f‖` over `(a, ∞)`
  have hfin : ∫⁻ x in Set.Ioi a, ‖f x‖ₑ < ⊤ := hIa.hasFiniteIntegral
  -- but `f ≥ m > 0` there, so that integral dominates `m · volume (a,∞) = ∞`
  have key : ∫⁻ x in Set.Ioi a, (ENNReal.ofReal m) ≤ ∫⁻ x in Set.Ioi a, ‖f x‖ₑ := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi (fun _ => (ENNReal.ofReal m)),
        ← MeasureTheory.lintegral_indicator measurableSet_Ioi (fun x => ‖f x‖ₑ)]
    apply MeasureTheory.lintegral_mono
    intro x
    by_cases hx : x ∈ Set.Ioi a
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Real.enorm_eq_ofReal_abs,
          abs_of_pos (lt_of_lt_of_le hm (hf x hx))]
      exact ENNReal.ofReal_le_ofReal (hf x hx)
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have htop : ∫⁻ x in Set.Ioi a, (ENNReal.ofReal m) = ⊤ := by
    rw [MeasureTheory.setLIntegral_const, Real.volume_Ioi,
        ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hm)]
  rw [htop] at key
  exact (not_le.mpr hfin) key

end Work.FTS.EllipticEst
