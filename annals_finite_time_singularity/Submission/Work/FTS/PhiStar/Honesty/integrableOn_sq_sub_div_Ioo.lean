import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem integrableOn_sq_sub_div_Ioo {c φ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hc : AEMeasurable c) (hφcont : Continuous φ)
    (hφsupp : ∀ t : ℝ, t ∉ Set.Icc a b → φ t = 0)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (φ t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1) := by
  -- `φ` is continuous with support in the compact `[a, b]`, hence bounded by some `M ≥ 0`.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hφcont.continuousOn
  let M : ℝ := max C 0
  have hM0 : 0 ≤ M := le_max_right C 0
  have hbdd : ∀ t : ℝ, |φ t| ≤ M := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · have h := hC t ht
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left C 0)
    · rw [hφsupp t ht, abs_zero]
      exact hM0
  -- Since `a > 0`, on the support of `φ` we have `t ≥ a`, hence `t ^ 4 ≥ a ^ 4 > 0`.
  have hφdiv : ∀ t : ℝ, (φ t) ^ 2 / t ^ 4 ≤ M ^ 2 / a ^ 4 := by
    intro t
    by_cases h0 : φ t = 0
    · rw [h0]
      have : (0 : ℝ) ≤ M ^ 2 / a ^ 4 := by positivity
      simpa using this
    · have ht : t ∈ Set.Icc a b := by
        by_contra hh
        exact h0 (hφsupp t hh)
      have hat : a ≤ t := ht.1
      have ha4 : (0 : ℝ) < a ^ 4 := by positivity
      have ht4 : (0 : ℝ) < t ^ 4 := pow_pos (lt_of_lt_of_le ha hat) 4
      have h1 : (φ t) ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbdd t) 2
      have h2 : 1 / t ^ 4 ≤ 1 / a ^ 4 :=
        one_div_le_one_div_of_le ha4 (pow_le_pow_left₀ ha.le hat 4)
      calc (φ t) ^ 2 / t ^ 4 = (φ t) ^ 2 * (1 / t ^ 4) := by ring
        _ ≤ M ^ 2 * (1 / a ^ 4) :=
            mul_le_mul h1 h2 (le_of_lt (one_div_pos.mpr ht4)) (sq_nonneg M)
        _ = M ^ 2 / a ^ 4 := by ring
  -- The dominating function `2 M ^ 2 / a ^ 4 + 2 (c t) ^ 2 / t ^ 4` is integrable on `(0, 1)`:
  -- the first term is a constant on a finite measure set, the second is a multiple of
  -- the integrable function given by the hypothesis `hnear`.
  have hD : MeasureTheory.IntegrableOn
      (fun t : ℝ => 2 * M ^ 2 / a ^ 4 + 2 * ((c t) ^ 2 / t ^ 4)) (Set.Ioo 0 1) := by
    have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => 2 * M ^ 2 / a ^ 4) (Set.Ioo 0 1) := by
      refine MeasureTheory.integrableOn_const (s := Set.Ioo 0 1) ?_
      rw [Real.volume_Ioo]
      simp
    have hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => 2 * ((c t) ^ 2 / t ^ 4)) (Set.Ioo 0 1) :=
      hnear.const_mul 2
    exact hconst.add hc2
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => (φ t - c t) ^ 2 / t ^ 4)
      (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := by
    have h1 : AEMeasurable (fun t : ℝ => φ t - c t)
        (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
      (hφcont.aemeasurable.mono_measure MeasureTheory.Measure.restrict_le_self).sub
        (hc.mono_measure MeasureTheory.Measure.restrict_le_self)
    have h2 : AEMeasurable (fun t : ℝ => (φ t - c t) ^ 2 / t ^ 4)
        (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
      (h1.pow_const 2).div (aemeasurable_id.pow_const 4)
    exact h2.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hD hmeas ?_
  filter_upwards with t
  have hpt : (φ t - c t) ^ 2 / t ^ 4 ≤ 2 * M ^ 2 / a ^ 4 + 2 * ((c t) ^ 2 / t ^ 4) := by
    have h1 : (φ t - c t) ^ 2 ≤ 2 * (φ t) ^ 2 + 2 * (c t) ^ 2 := by
      nlinarith [sq_nonneg (φ t + c t)]
    have h2 : (2 * (φ t) ^ 2 + 2 * (c t) ^ 2) / t ^ 4
        = 2 * ((φ t) ^ 2 / t ^ 4) + 2 * ((c t) ^ 2 / t ^ 4) := by ring
    have h3 : 2 * ((φ t) ^ 2 / t ^ 4) ≤ 2 * (M ^ 2 / a ^ 4) :=
      mul_le_mul_of_nonneg_left (hφdiv t) (by norm_num)
    calc (φ t - c t) ^ 2 / t ^ 4 ≤ (2 * (φ t) ^ 2 + 2 * (c t) ^ 2) / t ^ 4 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = 2 * ((φ t) ^ 2 / t ^ 4) + 2 * ((c t) ^ 2 / t ^ 4) := h2
      _ ≤ 2 * (M ^ 2 / a ^ 4) + 2 * ((c t) ^ 2 / t ^ 4) := by linarith
      _ = 2 * M ^ 2 / a ^ 4 + 2 * ((c t) ^ 2 / t ^ 4) := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hpt

end Work.FTS.PhiStar.Honesty
