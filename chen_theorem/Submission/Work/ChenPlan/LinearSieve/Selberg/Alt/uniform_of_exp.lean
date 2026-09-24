import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law

/-!
# The law of `exp(-E)` for `E` standard exponential is uniform on `(0,1)`

`cUnif` (see `Selberg/Alt/refsum_law.lean`) is the push-forward of the standard exponential
law `expLaw = expMeasure 1` under `t ↦ exp (-t)`.  Equivalently, the law of `U = e^{-E}`
is Lebesgue measure restricted to `(0,1)`.

The proof compares the values on the left-infinite intervals `(-∞, a]`: for `a ≤ 0` both
sides give `1`, for `0 < a < 1` both give `1 - a` (using the exponential CDF
`cdf (expMeasure 1) x = 1 - exp (-x)` for `x ≥ 0`), and for `a ≥ 1` both give `0`.
Since both measures are finite on `ℝ`, `Measure.ext_of_Ici` concludes.
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open MeasureTheory Set
open scoped ENNReal

noncomputable section

lemma measurable_exp_neg : Measurable (fun t : ℝ => Real.exp (-t)) := by fun_prop

instance instCUnifIsProbabilityMeasure : IsProbabilityMeasure cUnif := by
  rw [cUnif]
  exact (Measure.isProbabilityMeasure_map_iff measurable_exp_neg.aemeasurable).mpr inferInstance

lemma cUnif_Ici (a : ℝ) : cUnif (Ici a) = volume.restrict (Ioo (0:ℝ) 1) (Ici a) := by
  rw [cUnif, Measure.map_apply measurable_exp_neg measurableSet_Ici,
    Measure.restrict_apply measurableSet_Ici]
  rcases le_or_gt a 0 with ha | ha
  · -- `a ≤ 0`: the preimage is all of `ℝ`, and `(0,1) ⊆ (a,∞)`
    have hpre : (fun t : ℝ => Real.exp (-t)) ⁻¹' Ici a = Set.univ := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]
      exact le_trans ha (Real.exp_pos (-t)).le
    have hsub : Ioo (0:ℝ) 1 ⊆ Ici a := fun x hx => le_trans ha hx.1.le
    rw [hpre, Set.inter_eq_right.mpr hsub, Real.volume_Ioo, measure_univ]
    norm_num
  · have hpre : (fun t : ℝ => Real.exp (-t)) ⁻¹' Ici a = Iic (-Real.log a) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
      rw [← Real.log_le_iff_le_exp ha]
      constructor <;> intro h <;> linarith
    rw [hpre]
    rcases lt_or_ge a 1 with ha1 | ha1
    · -- `0 < a < 1`
      have hcdf : ProbabilityTheory.cdf expLaw (-Real.log a) = 1 - a := by
        rw [expLaw, ProbabilityTheory.cdf_expMeasure_eq (by norm_num : (0:ℝ) < 1)]
        rw [if_pos (by linarith [Real.log_neg ha ha1] : (0:ℝ) ≤ -Real.log a)]
        rw [one_mul, neg_neg, Real.exp_log ha]
      have hint : Ici a ∩ Ioo (0:ℝ) 1 = Ico a 1 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioo, Set.mem_Ico]
        constructor
        · intro h; exact ⟨h.1, h.2.2⟩
        · intro h; exact ⟨h.1, ⟨by linarith [h.1], h.2⟩⟩
      rw [← ProbabilityTheory.ofReal_cdf (μ := expLaw) (-Real.log a), hcdf, hint,
        Real.volume_Ico]
    · -- `1 ≤ a`
      have hcdf : ProbabilityTheory.cdf expLaw (-Real.log a) = 0 := by
        rw [expLaw, ProbabilityTheory.cdf_expMeasure_eq (by norm_num : (0:ℝ) < 1)]
        rcases eq_or_lt_of_le ha1 with h1 | h1
        · rw [← h1, Real.log_one, neg_zero, if_pos le_rfl]
          norm_num
        · rw [if_neg (by linarith [Real.log_pos h1] : ¬ (0:ℝ) ≤ -Real.log a)]
      have hint : Ici a ∩ Ioo (0:ℝ) 1 = (∅ : Set ℝ) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioo, Set.mem_empty_iff_false,
          iff_false]
        intro h
        linarith [h.1, h.2.2]
      rw [← ProbabilityTheory.ofReal_cdf (μ := expLaw) (-Real.log a), hcdf, hint, measure_empty]
      simp

theorem uniform_of_exp : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1) :=
  Measure.ext_of_Ici cUnif _ cUnif_Ici

end

end Work.ChenPlan.LinearSieve.Selberg.Alt
