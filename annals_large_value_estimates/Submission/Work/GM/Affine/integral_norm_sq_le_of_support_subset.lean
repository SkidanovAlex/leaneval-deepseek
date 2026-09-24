import Mathlib

namespace Work.GM.Affine

open MeasureTheory Set

theorem integral_norm_sq_le_of_support_subset (h : ℝ → ℂ) (K : Set ℝ) (ε : ℝ)
    (hK : MeasurableSet K) (hKf : MeasureTheory.volume K < ⊤) (hε : 0 ≤ ε)
    (hsur : ∀ x ∉ K, h x = 0) (hbd : ∀ x, ‖h x‖ ≤ ε) :
    ∫ x, ‖h x‖ ^ 2 ≤ ε ^ 2 * (MeasureTheory.volume K).toReal := by
  -- Pointwise domination by `ε ^ 2 * 1_K`.
  have hle : ∀ x, ‖h x‖ ^ 2 ≤ ε ^ 2 * K.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, mul_one]
      nlinarith [hbd x, norm_nonneg (h x), hε]
    · rw [Set.indicator_of_notMem hx, mul_zero, hsur x hx]
      simp
  -- The dominating function is integrable since `K` has finite measure.
  have hIntOn : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) K MeasureTheory.volume := by
    rw [MeasureTheory.integrableOn_const_iff]
    exact Or.inr hKf
  have hIntInd : MeasureTheory.Integrable (fun x => K.indicator (fun _ => (1 : ℝ)) x)
      MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff hK).mpr hIntOn
  have hg : MeasureTheory.Integrable
      (fun x => ε ^ 2 * K.indicator (fun _ => (1 : ℝ)) x) MeasureTheory.volume :=
    hIntInd.const_mul (ε ^ 2)
  have hgval : ∫ x, ε ^ 2 * K.indicator (fun _ => (1 : ℝ)) x
      = ε ^ 2 * (MeasureTheory.volume K).toReal := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_indicator_const (e := (1 : ℝ)) hK]
    simp [MeasureTheory.measureReal_def]
  by_cases hint : MeasureTheory.Integrable (fun x => ‖h x‖ ^ 2) MeasureTheory.volume
  · calc ∫ x, ‖h x‖ ^ 2 ≤ ∫ x, ε ^ 2 * K.indicator (fun _ => (1 : ℝ)) x :=
        MeasureTheory.integral_mono_ae hint hg (Filter.Eventually.of_forall hle)
      _ = ε ^ 2 * (MeasureTheory.volume K).toReal := hgval
  · rw [MeasureTheory.integral_undef hint]
    exact mul_nonneg (sq_nonneg ε) ENNReal.toReal_nonneg

end Work.GM.Affine
