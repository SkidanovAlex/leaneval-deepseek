import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

theorem analyticAt_coefFun {n K : ℕ} (d : Fin K → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (ha : ∀ i j, AnalyticAt ℝ (a i j) 0)
    (t : Fin (∑ i, d i)) :
    AnalyticAt ℝ (fun x' : Fin n → ℝ => Work.WilC4aCS.coefFun d a x' t) 0 := by
  -- `coefFun d a x' t` is definitionally the component `a i j x'` selected by the
  -- inverse of the flattening equivalence `finSigmaFinEquiv`, so the claim is exactly
  -- the corresponding hypothesis.
  exact ha (finSigmaFinEquiv.symm t).1 (finSigmaFinEquiv.symm t).2

end Work.WilC4aCS
