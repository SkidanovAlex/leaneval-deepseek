/-
# The deviation square-function bound, assembled from the Hörmander estimate of `lacDevHormanderAlt`

This re-assembles the deviation half of `Work.KMTAreas.A7.lacunaryBumpDilationVar` from

* the uniform symbol bound `lacDevSymBoundAlt`,
* the `ℓ²` bound `lacDevL2`,
* the discrete Hörmander condition `lacDevHormanderAlt`,

via the discrete Calderón–Zygmund reduction `lacDilDevSqSum_of_inputs`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacDevSymBoundAlt
import Submission.Work.KMTAreas.A7.lacDevHormanderAlt

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The deviation square function is `ℓᵖ`-bounded (assembled from the CZ inputs). -/
theorem lacDilDevSqSumViaAlt (p : ℝ) (hp : 1 < p) (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm
          (fun x : ℤ => (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  obtain ⟨Csym, hCsympos, hsym⟩ := lacDevSymBoundAlt K
  obtain ⟨A2, hA2pos, hA2⟩ := lacDevL2 K Csym hCsympos hsym
  obtain ⟨Ak, hAkpos, hAk⟩ := lacDevHormanderAlt K
  exact lacDilDevSqSum_of_inputs p hp K Csym hCsympos hsym ⟨A2, hA2pos, hA2⟩ ⟨Ak, hAkpos, hAk⟩

end

end Work.KMTAreas.A7
