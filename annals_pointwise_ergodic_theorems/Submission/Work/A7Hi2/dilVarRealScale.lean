import Mathlib
import Submission.Work.A7Hi2.symDiffR_overlap
import Submission.Work.A7Hi2.linDiffKernR_size
import Submission.Work.A7Hi2.linDiffKernR_hormander
import Submission.Work.A7Hi2.linDiffKernR_l2
import Submission.Work.A7Hi2.diffSqSumR_of_inputs

namespace Work.A7Hi2

theorem dilVarRealScale (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ1 : ∀ n : ℕ, 1 ≤ σ n)
      (hσ2 : ∀ n : ℕ, 2 * σ n ≤ σ (n + 1)) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / σ n) * K ((j : ℝ) / (σ n)) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨Csym, hCsympos, hsym⟩ := symDiffR_overlap K
  obtain ⟨A₂, hA₂pos, hl2⟩ := linDiffKernR_l2 K Csym hCsympos hsym
  obtain ⟨B, hBpos, hsize⟩ := linDiffKernR_size K
  obtain ⟨Ak, hAkpos, hhorm⟩ := linDiffKernR_hormander K
  obtain ⟨C, hCpos, hSq⟩ :=
    diffSqSumR_of_inputs p hp K ⟨B, hBpos, hsize⟩ ⟨Ak, hAkpos, hhorm⟩ ⟨A₂, hA₂pos, hl2⟩
  exact dilVarRealScale_of_sqSum p hp r hr K ⟨C, hCpos, hSq⟩

end Work.A7Hi2
