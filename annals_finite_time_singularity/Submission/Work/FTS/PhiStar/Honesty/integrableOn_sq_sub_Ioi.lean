import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- If `c²` is integrable on `(1,∞)` and `φ` is continuous with support in the bounded
interval `[a,b]`, then `(φ - c)²` is integrable on `(1,∞)`: the only unbounded factor `c`
multiplies `φ`, which vanishes off the compact set `Icc a b`, where `c²` is integrable
(finite measure) as a restriction of the hypothesis. -/
theorem integrableOn_sq_sub_Ioi {c φ : ℝ → ℝ} {a b : ℝ}
    (hc : AEMeasurable c) (hφcont : Continuous φ)
    (hφsupp : ∀ t : ℝ, t ∉ Set.Icc a b → φ t = 0)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (φ t - c t) ^ 2) (Set.Ioi 1) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hφcont.continuousOn
  set C : ℝ := max K 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCb : ∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ C := fun t ht => le_trans (hK t ht) (le_max_left _ _)
  have hfin : volume (Set.Ioi (1:ℝ) ∩ Set.Icc a b) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.inter_subset_right)) isCompact_Icc.measure_lt_top
  -- on the bounded part `(1,∞) ∩ [a,b]` everything is dominated by `2C² + 2c²`
  have hA : MeasureTheory.IntegrableOn (fun t : ℝ => (φ t - c t) ^ 2)
      (Set.Ioi 1 ∩ Set.Icc a b) := by
    have hdom : Integrable (fun t : ℝ => 2 * C^2 + 2 * (c t)^2)
        (volume.restrict (Set.Ioi 1 ∩ Set.Icc a b)) := by
      have h1 : Integrable (fun t : ℝ => 2 * (c t)^2)
          (volume.restrict (Set.Ioi 1 ∩ Set.Icc a b)) :=
        Integrable.const_mul (hfar.mono_set Set.inter_subset_left) 2
      have h2 : Integrable (fun _ : ℝ => 2 * C^2)
          (volume.restrict (Set.Ioi 1 ∩ Set.Icc a b)) :=
        integrableOn_const (C := 2 * C^2) hfin.ne (by finiteness)
      exact h2.add h1
    refine hdom.mono' ?_ ?_
    · have hme : AEMeasurable (fun t : ℝ => (φ t - c t) ^ 2) :=
        (hφcont.aemeasurable.sub hc).pow_const 2
      exact (hme.restrict).aestronglyMeasurable
    · filter_upwards with t
      have hφb : (φ t)^2 ≤ C^2 := by
        by_cases ht : t ∈ Set.Icc a b
        · have h1 : |φ t| ≤ C := by simpa [Real.norm_eq_abs] using hCb t ht
          calc (φ t)^2 = |φ t|^2 := (sq_abs (φ t)).symm
            _ ≤ C^2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        · simpa [hφsupp t ht] using sq_nonneg C
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (φ t - c t))]
      nlinarith [sq_nonneg (φ t + c t), hφb]
  -- off `[a,b]` we have `φ = 0`, so this is just `c²`
  have hB : MeasureTheory.IntegrableOn (fun t : ℝ => (φ t - c t) ^ 2)
      (Set.Ioi 1 ∩ (Set.Icc a b)ᶜ) := by
    have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (c t)^2)
        (Set.Ioi 1 ∩ (Set.Icc a b)ᶜ) := hfar.mono_set Set.inter_subset_left
    refine hbase.congr_fun ?_ (measurableSet_Ioi.inter measurableSet_Icc.compl)
    intro t ht
    show (c t)^2 = (φ t - c t)^2
    rw [hφsupp t ht.2]
    ring
  have h := hA.union hB
  rwa [Set.inter_union_compl] at h

end Work.FTS.PhiStar.Honesty
