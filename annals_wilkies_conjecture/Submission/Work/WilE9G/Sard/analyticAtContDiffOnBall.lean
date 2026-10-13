import Mathlib
import Submission.Work.WilE9G.Sard.FlatDefs

namespace Work.WilE9G.Sard

open scoped ContDiff

/-- The smoothness exponent `(↑n : WithTop ℕ∞)` coming from a natural number is not `∞`. -/
private lemma natCast_withTop_ne_infty (n : ℕ) : (↑n : WithTop ℕ∞) ≠ ∞ := by
  have h : (↑n : WithTop ℕ∞) = ((n : ℕ∞) : WithTop ℕ∞) := rfl
  rw [h, ne_eq, WithTop.coe_inj]
  exact (ENat.natCast_lt_top n).ne

/-- A function analytic at a point `x` is `C^n` on some ball around `x`. -/
theorem analyticAtContDiffOnBall {d m n : ℕ} {f : (Fin d → ℝ) → (Fin m → ℝ)} {x : Fin d → ℝ}
    (hx : AnalyticAt ℝ f x) :
    ∃ R > 0, ContDiffOn ℝ (↑n : WithTop ℕ∞) f (Metric.ball x R) := by
  have hcont : ContDiffWithinAt ℝ (↑n : WithTop ℕ∞) f Set.univ x := hx.contDiffAt
  rw [contDiffWithinAt_iff_contDiffOn_nhds (natCast_withTop_ne_infty n)] at hcont
  rw [Set.insert_eq_of_mem (Set.mem_univ x), nhdsWithin_univ] at hcont
  rcases hcont with ⟨u, hu, hcu⟩
  rcases Metric.mem_nhds_iff.1 hu with ⟨R, hRpos, hRu⟩
  exact ⟨R, hRpos, hcu.mono hRu⟩

end Work.WilE9G.Sard
