import Mathlib
import Submission.Work.CNum.blkDef

namespace Work.CNum

open MeasureTheory

theorem blk_step_integral {N : ℕ} (c : Fin N → Fin N → ℝ) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ] (hμ : ∀ k : Fin N, μ (blk N k) = ENNReal.ofReal (1/(N:ℝ))) :
    ∫ z, (∑ k : Fin N, ∑ k' : Fin N,
        (blk N k ×ˢ blk N k').indicator (fun _ => c k k') z) ∂(μ.prod μ)
      = ∑ k : Fin N, ∑ k' : Fin N, (1/(N:ℝ)^2) * c k k' := by
  have hsq : (1/(N:ℝ)) * (1/(N:ℝ)) = 1/(N:ℝ)^2 := by
    rw [← sq, ← one_div_pow]
  have hN : ∀ k k' : Fin N,
      (μ.prod μ) (blk N k ×ˢ blk N k') = ENNReal.ofReal (1/(N:ℝ)^2) := by
    intro k k'
    rw [Measure.prod_prod, hμ k, hμ k', ← ENNReal.ofReal_mul (by positivity), hsq]
  have hreal : ∀ k k' : Fin N,
      (μ.prod μ).real (blk N k ×ˢ blk N k') = 1/(N:ℝ)^2 := by
    intro k k'
    rw [Measure.real_def, hN k k', ENNReal.toReal_ofReal (by positivity)]
  have hone : ∀ k k' : Fin N,
      ∫ z, (blk N k ×ˢ blk N k').indicator (fun _ => c k k') z ∂(μ.prod μ)
        = (1/(N:ℝ)^2) * c k k' := by
    intro k k'
    rw [integral_indicator_const (c k k') ((blk_measurable N k).prod (blk_measurable N k')),
      hreal k k', smul_eq_mul]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k' _
      exact hone k k'
    · intro k' _
      exact Integrable.indicator (integrable_const _) ((blk_measurable N k).prod (blk_measurable N k'))
  · intro k _
    exact MeasureTheory.integrable_finsetSum _ fun k' _ =>
      Integrable.indicator (integrable_const _) ((blk_measurable N k).prod (blk_measurable N k'))

end Work.CNum
