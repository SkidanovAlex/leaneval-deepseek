import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

theorem analyticAt_snoc {n : ℕ} {p : ℝ → Fin n → ℝ} {x : ℝ → ℝ} {s₀ : ℝ}
    (hp : AnalyticAt ℝ p s₀) (hx : AnalyticAt ℝ x s₀) :
    AnalyticAt ℝ (fun s => (Fin.snoc (p s) (x s) : Fin (n + 1) → ℝ)) s₀ := by
  -- `AnalyticAt` into a finite product is componentwise (`analyticAt_pi_iff`), so it suffices to
  -- check the `n + 1` coordinates of the snoc'd family.  `Fin.lastCases` splits those into the
  -- final coordinate (`x`) and the first `n` coordinates (`p`).
  refine analyticAt_pi_iff.mpr (fun i => ?_)
  refine Fin.lastCases ?_ ?_ i
  · simpa only [Fin.snoc_last] using hx
  · intro i
    simpa only [Fin.snoc_castSucc] using (analyticAt_pi_iff.mp hp i)

end Work.WilC4aCS
