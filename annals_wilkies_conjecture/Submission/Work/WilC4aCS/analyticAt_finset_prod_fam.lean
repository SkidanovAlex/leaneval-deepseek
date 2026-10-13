import Mathlib
import Submission.Work.WilC4aCS.Defs

open scoped BigOperators

namespace Work.WilC4aCS

/-- A finite product of functions analytic at `0` is analytic at `0`. -/
theorem analyticAt_finset_prod_fam {m l : ℕ} (g : Fin l → (Fin m → ℝ) → ℝ)
    (hg : ∀ j, AnalyticAt ℝ (g j) 0) :
    AnalyticAt ℝ (fun x : Fin m → ℝ => ∏ j, g j x) 0 := by
  have h := Finset.analyticAt_prod (𝕜 := ℝ) (A := ℝ) (Finset.univ : Finset (Fin l))
    (f := fun j x => g j x) (fun j _ => hg j)
  have h2 : (∏ j : Fin l, (fun x : Fin m → ℝ => g j x)) = fun x : Fin m → ℝ => ∏ j, g j x := by
    funext x
    rw [Finset.prod_apply]
  rw [h2] at h
  exact h

end Work.WilC4aCS
