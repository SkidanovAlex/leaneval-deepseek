import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun

namespace Work.LinnikAreas.Density4

/-- `gT θ lam` is supported in `[-gammaT θ lam, gammaT θ lam]` and equals
`lam * (1 + tan²θ) * (cos (zetaT θ lam * t) - cos θ)` there, i.e. it is the
indicator of that interval applied to a continuous (hence measurable) function. -/
lemma gT_eq_indicator (θ lam : ℝ) :
    (fun t : ℝ => gT θ lam t)
      = Set.indicator (Set.Icc (-(gammaT θ lam)) (gammaT θ lam))
          (fun t => lam * (1 + Real.tan θ ^ 2) * (Real.cos (zetaT θ lam * t) - Real.cos θ)) := by
  funext t
  rw [gT]
  by_cases ht : |t| ≤ gammaT θ lam
  · rw [if_pos ht, Set.indicator_of_mem
      (show t ∈ Set.Icc (-(gammaT θ lam)) (gammaT θ lam) by
        rw [Set.mem_Icc]; exact abs_le.mp ht)]
  · rw [if_neg ht, Set.indicator_of_notMem
      (show t ∉ Set.Icc (-(gammaT θ lam)) (gammaT θ lam) by
        rw [Set.mem_Icc]; intro h; exact ht (abs_le.mpr h))]

theorem gT_integrable {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    MeasureTheory.Integrable (fun t : ℝ => gT θ lam t) := by
  have hγ : 0 < gammaT θ lam := gammaT_pos hθ1 hθ2 hlam
  rw [gT_eq_indicator θ lam]
  apply MeasureTheory.IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply MeasureTheory.IntegrableOn.of_bound (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  · fun_prop
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.cos (zetaT θ lam * x) - Real.cos θ| ≤ 2 := by
      have ha := Real.abs_cos_le_one (zetaT θ lam * x)
      have hb := Real.abs_cos_le_one θ
      calc |Real.cos (zetaT θ lam * x) - Real.cos θ|
          ≤ |Real.cos (zetaT θ lam * x) - 0| + |0 - Real.cos θ| := abs_sub_le _ _ _
        _ ≤ 1 + 1 := by rw [sub_zero, zero_sub, abs_neg]; exact add_le_add ha hb
        _ = 2 := by norm_num
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

end Work.LinnikAreas.Density4
