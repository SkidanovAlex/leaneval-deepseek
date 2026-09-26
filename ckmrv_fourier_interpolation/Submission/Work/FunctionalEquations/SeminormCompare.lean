import Mathlib
import Submission.Work.FunctionalEquations.SeminormCompareMulti

namespace Work.FunctionalEquations

open scoped SchwartzMap ContDiff

/-- For every `P` the Schwartz seminorms of order `(a, b)` with `a + b ≤ P` are bounded by
the two extremal seminorms of order `P`, namely the weighted value seminorm `(P, 0)` and the
top derivative seminorm `(0, P)`. -/
theorem SeminormCompare {n : ℕ} [NeZero n] (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (a b : ℕ), a + b ≤ P →
      (SchwartzMap.seminorm ℂ a b) g ≤
        C * ((SchwartzMap.seminorm ℂ P 0) g + (SchwartzMap.seminorm ℂ 0 P) g) := by
  obtain ⟨C, hCnn, hC⟩ := seminorm_bound_aux (n := n) P
  refine ⟨C, hCnn, ?_⟩
  intro g a b hab
  have hMnn : (0:ℝ) ≤ C * ((SchwartzMap.seminorm ℂ P 0) g + (SchwartzMap.seminorm ℂ 0 P) g) :=
    mul_nonneg hCnn (add_nonneg (apply_nonneg _ g) (apply_nonneg _ g))
  refine SchwartzMap.seminorm_le_bound ℂ a b g hMnn (fun x => ?_)
  have hA : ∀ y, ‖y‖^P * ‖(g : EuclideanSpace ℝ (Fin n) → ℂ) y‖ ≤
      (SchwartzMap.seminorm ℂ P 0) g := by
    intro y
    have h := SchwartzMap.le_seminorm ℂ P 0 g y
    simpa using h
  have hB : ∀ y, ‖iteratedFDeriv ℝ P (g : EuclideanSpace ℝ (Fin n) → ℂ) y‖ ≤
      (SchwartzMap.seminorm ℂ 0 P) g := by
    intro y
    have h := SchwartzMap.le_seminorm ℂ 0 P g y
    simpa using h
  have hg : ContDiff ℝ ∞ (g : EuclideanSpace ℝ (Fin n) → ℂ) := g.smooth ⊤
  exact hC ℂ (g : EuclideanSpace ℝ (Fin n) → ℂ) hg ((SchwartzMap.seminorm ℂ P 0) g)
    ((SchwartzMap.seminorm ℂ 0 P) g) (apply_nonneg _ g) (apply_nonneg _ g) hA hB a b hab x

end Work.FunctionalEquations
